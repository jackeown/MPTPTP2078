%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0937+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:58 EST 2020

% Result     : Theorem 34.98s
% Output     : CNFRefutation 34.98s
% Verified   : 
% Statistics : Number of formulae       :   53 (  76 expanded)
%              Number of clauses        :   20 (  23 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   17
%              Number of atoms          :  228 ( 371 expanded)
%              Number of equality atoms :   45 (  67 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   17 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f2863,plain,(
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

fof(f2864,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2863])).

fof(f3977,plain,(
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
    inference(nnf_transformation,[],[f2864])).

fof(f3978,plain,(
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
    inference(flattening,[],[f3977])).

fof(f3979,plain,(
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
    inference(rectify,[],[f3978])).

fof(f3980,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK459(X0,X1),sK460(X0,X1))
          | ~ r2_hidden(k4_tarski(sK459(X0,X1),sK460(X0,X1)),X1) )
        & ( r1_tarski(sK459(X0,X1),sK460(X0,X1))
          | r2_hidden(k4_tarski(sK459(X0,X1),sK460(X0,X1)),X1) )
        & r2_hidden(sK460(X0,X1),X0)
        & r2_hidden(sK459(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3981,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK459(X0,X1),sK460(X0,X1))
              | ~ r2_hidden(k4_tarski(sK459(X0,X1),sK460(X0,X1)),X1) )
            & ( r1_tarski(sK459(X0,X1),sK460(X0,X1))
              | r2_hidden(k4_tarski(sK459(X0,X1),sK460(X0,X1)),X1) )
            & r2_hidden(sK460(X0,X1),X0)
            & r2_hidden(sK459(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK459,sK460])],[f3979,f3980])).

fof(f6544,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3981])).

fof(f7818,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f6544])).

fof(f1421,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6551,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1421])).

fof(f1146,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2555,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1146])).

fof(f3649,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2555])).

fof(f3650,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f3649])).

fof(f3651,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK286(X0),sK286(X0)),X0)
        & r2_hidden(sK286(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3652,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK286(X0),sK286(X0)),X0)
            & r2_hidden(sK286(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK286])],[f3650,f3651])).

fof(f5944,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | r2_hidden(sK286(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3652])).

fof(f5945,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ r2_hidden(k4_tarski(sK286(X0),sK286(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3652])).

fof(f6546,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3981])).

fof(f7816,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f6546])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2949,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f2950,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2949])).

fof(f4054,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2950])).

fof(f7517,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f4054])).

fof(f1424,conjecture,(
    ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1425,negated_conjecture,(
    ~ ! [X0] : v1_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f1424])).

fof(f2865,plain,(
    ? [X0] : ~ v1_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f1425])).

fof(f3986,plain,
    ( ? [X0] : ~ v1_relat_2(k1_wellord2(X0))
   => ~ v1_relat_2(k1_wellord2(sK463)) ),
    introduced(choice_axiom,[])).

fof(f3987,plain,(
    ~ v1_relat_2(k1_wellord2(sK463)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK463])],[f2865,f3986])).

fof(f6555,plain,(
    ~ v1_relat_2(k1_wellord2(sK463)) ),
    inference(cnf_transformation,[],[f3987])).

cnf(c_2539,plain,
    ( ~ v1_relat_1(k1_wellord2(X0))
    | k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(cnf_transformation,[],[f7818])).

cnf(c_2540,plain,
    ( v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f6551])).

cnf(c_12576,plain,
    ( k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2539,c_2540])).

cnf(c_1941,plain,
    ( r2_hidden(sK286(X0),k3_relat_1(X0))
    | v1_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5944])).

cnf(c_114623,plain,
    ( r2_hidden(sK286(X0),k3_relat_1(X0)) = iProver_top
    | v1_relat_2(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1941])).

cnf(c_121356,plain,
    ( r2_hidden(sK286(k1_wellord2(X0)),X0) = iProver_top
    | v1_relat_2(k1_wellord2(X0)) = iProver_top
    | v1_relat_1(k1_wellord2(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12576,c_114623])).

cnf(c_2549,plain,
    ( v1_relat_1(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2540])).

cnf(c_1940,plain,
    ( ~ r2_hidden(k4_tarski(sK286(X0),sK286(X0)),X0)
    | v1_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5945])).

cnf(c_2537,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
    | ~ v1_relat_1(k1_wellord2(X2)) ),
    inference(cnf_transformation,[],[f7816])).

cnf(c_118091,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2540,c_2537])).

cnf(c_120472,plain,
    ( ~ r1_tarski(sK286(k1_wellord2(X0)),sK286(k1_wellord2(X0)))
    | ~ r2_hidden(sK286(k1_wellord2(X0)),X0)
    | v1_relat_2(k1_wellord2(X0))
    | ~ v1_relat_1(k1_wellord2(X0)) ),
    inference(resolution,[status(thm)],[c_1940,c_118091])).

cnf(c_120478,plain,
    ( v1_relat_2(k1_wellord2(X0))
    | ~ r2_hidden(sK286(k1_wellord2(X0)),X0)
    | ~ r1_tarski(sK286(k1_wellord2(X0)),sK286(k1_wellord2(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_120472,c_2540])).

cnf(c_120479,plain,
    ( ~ r1_tarski(sK286(k1_wellord2(X0)),sK286(k1_wellord2(X0)))
    | ~ r2_hidden(sK286(k1_wellord2(X0)),X0)
    | v1_relat_2(k1_wellord2(X0)) ),
    inference(renaming,[status(thm)],[c_120478])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7517])).

cnf(c_120487,plain,
    ( ~ r2_hidden(sK286(k1_wellord2(X0)),X0)
    | v1_relat_2(k1_wellord2(X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_120479,c_69])).

cnf(c_120488,plain,
    ( r2_hidden(sK286(k1_wellord2(X0)),X0) != iProver_top
    | v1_relat_2(k1_wellord2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_120487])).

cnf(c_133671,plain,
    ( v1_relat_2(k1_wellord2(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_121356,c_2549,c_120488])).

cnf(c_2544,negated_conjecture,
    ( ~ v1_relat_2(k1_wellord2(sK463)) ),
    inference(cnf_transformation,[],[f6555])).

cnf(c_114101,plain,
    ( v1_relat_2(k1_wellord2(sK463)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2544])).

cnf(c_133678,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_133671,c_114101])).

%------------------------------------------------------------------------------
