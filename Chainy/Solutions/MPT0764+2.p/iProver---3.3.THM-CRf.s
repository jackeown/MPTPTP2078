%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0764+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:52 EST 2020

% Result     : Theorem 27.66s
% Output     : CNFRefutation 27.66s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 171 expanded)
%              Number of clauses        :   31 (  40 expanded)
%              Number of leaves         :    8 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  233 ( 937 expanded)
%              Number of equality atoms :   59 ( 163 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1141,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1142,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ( r2_hidden(X3,X1)
                         => r2_hidden(k4_tarski(X2,X3),X0) )
                      & r2_hidden(X2,X1) )
                & k1_xboole_0 != X1
                & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1141])).

fof(f2259,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1142])).

fof(f2260,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f2259])).

fof(f3043,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1) )
     => ( ~ r2_hidden(k4_tarski(X2,sK285(X2)),X0)
        & r2_hidden(sK285(X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f3042,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,sK284) )
            | ~ r2_hidden(X2,sK284) )
        & k1_xboole_0 != sK284
        & r1_tarski(sK284,k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3041,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                    & r2_hidden(X3,X1) )
                | ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1
            & r1_tarski(X1,k3_relat_1(X0)) )
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),sK283)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(sK283)) )
      & v2_wellord1(sK283)
      & v1_relat_1(sK283) ) ),
    introduced(choice_axiom,[])).

fof(f3044,plain,
    ( ! [X2] :
        ( ( ~ r2_hidden(k4_tarski(X2,sK285(X2)),sK283)
          & r2_hidden(sK285(X2),sK284) )
        | ~ r2_hidden(X2,sK284) )
    & k1_xboole_0 != sK284
    & r1_tarski(sK284,k3_relat_1(sK283))
    & v2_wellord1(sK283)
    & v1_relat_1(sK283) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK283,sK284,sK285])],[f2260,f3043,f3042,f3041])).

fof(f4991,plain,(
    ! [X2] :
      ( r2_hidden(sK285(X2),sK284)
      | ~ r2_hidden(X2,sK284) ) ),
    inference(cnf_transformation,[],[f3044])).

fof(f1146,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,X0)
       => ! [X2] :
            ~ ( ! [X3] :
                  ~ ( ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) )
                    & r2_hidden(X3,X2) )
              & k1_xboole_0 != X2
              & r1_tarski(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2265,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1146])).

fof(f2266,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2265])).

fof(f3047,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X2) )
          & r2_hidden(X3,X2) )
     => ( ! [X4] :
            ( r2_hidden(k4_tarski(sK286(X1,X2),X4),X1)
            | ~ r2_hidden(X4,X2) )
        & r2_hidden(sK286(X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f3048,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ! [X4] :
                ( r2_hidden(k4_tarski(sK286(X1,X2),X4),X1)
                | ~ r2_hidden(X4,X2) )
            & r2_hidden(sK286(X1,X2),X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK286])],[f2266,f3047])).

fof(f4999,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK286(X1,X2),X4),X1)
      | ~ r2_hidden(X4,X2)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3048])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3056,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5679,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK286(X1,X2),X4),X1)
      | ~ r2_hidden(X4,X2)
      | o_0_0_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f4999,f3056])).

fof(f1145,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2264,plain,(
    ! [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1145])).

fof(f3046,plain,(
    ! [X0] :
      ( ( ( r2_wellord1(X0,k3_relat_1(X0))
          | ~ v2_wellord1(X0) )
        & ( v2_wellord1(X0)
          | ~ r2_wellord1(X0,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2264])).

fof(f4997,plain,(
    ! [X0] :
      ( r2_wellord1(X0,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3046])).

fof(f4988,plain,(
    v2_wellord1(sK283) ),
    inference(cnf_transformation,[],[f3044])).

fof(f4987,plain,(
    v1_relat_1(sK283) ),
    inference(cnf_transformation,[],[f3044])).

fof(f4992,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK285(X2)),sK283)
      | ~ r2_hidden(X2,sK284) ) ),
    inference(cnf_transformation,[],[f3044])).

fof(f4989,plain,(
    r1_tarski(sK284,k3_relat_1(sK283)) ),
    inference(cnf_transformation,[],[f3044])).

fof(f4990,plain,(
    k1_xboole_0 != sK284 ),
    inference(cnf_transformation,[],[f3044])).

fof(f5677,plain,(
    o_0_0_xboole_0 != sK284 ),
    inference(definition_unfolding,[],[f4990,f3056])).

fof(f4998,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK286(X1,X2),X2)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3048])).

fof(f5680,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK286(X1,X2),X2)
      | o_0_0_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f4998,f3056])).

cnf(c_1924,negated_conjecture,
    ( ~ r2_hidden(X0,sK284)
    | r2_hidden(sK285(X0),sK284) ),
    inference(cnf_transformation,[],[f4991])).

cnf(c_87929,plain,
    ( r2_hidden(X0,sK284) != iProver_top
    | r2_hidden(sK285(X0),sK284) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_1934,plain,
    ( ~ r2_wellord1(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,X2)
    | r2_hidden(k4_tarski(sK286(X0,X2),X3),X0)
    | ~ v1_relat_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f5679])).

cnf(c_1932,plain,
    ( r2_wellord1(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4997])).

cnf(c_1927,negated_conjecture,
    ( v2_wellord1(sK283) ),
    inference(cnf_transformation,[],[f4988])).

cnf(c_21610,plain,
    ( r2_wellord1(X0,k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK283 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1932,c_1927])).

cnf(c_21611,plain,
    ( r2_wellord1(sK283,k3_relat_1(sK283))
    | ~ v1_relat_1(sK283) ),
    inference(unflattening,[status(thm)],[c_21610])).

cnf(c_1928,negated_conjecture,
    ( v1_relat_1(sK283) ),
    inference(cnf_transformation,[],[f4987])).

cnf(c_21613,plain,
    ( r2_wellord1(sK283,k3_relat_1(sK283)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21611,c_1928])).

cnf(c_21695,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k4_tarski(sK286(X3,X0),X2),X3)
    | ~ v1_relat_1(X3)
    | k3_relat_1(sK283) != X1
    | sK283 != X3
    | o_0_0_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1934,c_21613])).

cnf(c_21696,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK283))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(k4_tarski(sK286(sK283,X0),X1),sK283)
    | ~ v1_relat_1(sK283)
    | o_0_0_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_21695])).

cnf(c_21698,plain,
    ( r2_hidden(k4_tarski(sK286(sK283,X0),X1),sK283)
    | ~ r2_hidden(X1,X0)
    | ~ r1_tarski(X0,k3_relat_1(sK283))
    | o_0_0_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21696,c_1928])).

cnf(c_21699,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK283))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(k4_tarski(sK286(sK283,X0),X1),sK283)
    | o_0_0_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_21698])).

cnf(c_87828,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(X0,k3_relat_1(sK283)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(k4_tarski(sK286(sK283,X0),X1),sK283) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21699])).

cnf(c_1923,negated_conjecture,
    ( ~ r2_hidden(X0,sK284)
    | ~ r2_hidden(k4_tarski(X0,sK285(X0)),sK283) ),
    inference(cnf_transformation,[],[f4992])).

cnf(c_87930,plain,
    ( r2_hidden(X0,sK284) != iProver_top
    | r2_hidden(k4_tarski(X0,sK285(X0)),sK283) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1923])).

cnf(c_103032,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(X0,k3_relat_1(sK283)) != iProver_top
    | r2_hidden(sK286(sK283,X0),sK284) != iProver_top
    | r2_hidden(sK285(sK286(sK283,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_87828,c_87930])).

cnf(c_103039,plain,
    ( sK284 = o_0_0_xboole_0
    | r1_tarski(sK284,k3_relat_1(sK283)) != iProver_top
    | r2_hidden(sK286(sK283,sK284),sK284) != iProver_top ),
    inference(superposition,[status(thm)],[c_87929,c_103032])).

cnf(c_1926,negated_conjecture,
    ( r1_tarski(sK284,k3_relat_1(sK283)) ),
    inference(cnf_transformation,[],[f4989])).

cnf(c_1938,plain,
    ( r1_tarski(sK284,k3_relat_1(sK283)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1926])).

cnf(c_1925,negated_conjecture,
    ( o_0_0_xboole_0 != sK284 ),
    inference(cnf_transformation,[],[f5677])).

cnf(c_1935,plain,
    ( ~ r2_wellord1(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r2_hidden(sK286(X0,X2),X2)
    | ~ v1_relat_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f5680])).

cnf(c_21674,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(sK286(X2,X0),X0)
    | ~ v1_relat_1(X2)
    | k3_relat_1(sK283) != X1
    | sK283 != X2
    | o_0_0_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1935,c_21613])).

cnf(c_21675,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK283))
    | r2_hidden(sK286(sK283,X0),X0)
    | ~ v1_relat_1(sK283)
    | o_0_0_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_21674])).

cnf(c_21679,plain,
    ( r2_hidden(sK286(sK283,X0),X0)
    | ~ r1_tarski(X0,k3_relat_1(sK283))
    | o_0_0_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21675,c_1928])).

cnf(c_21680,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK283))
    | r2_hidden(sK286(sK283,X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_21679])).

cnf(c_102979,plain,
    ( ~ r1_tarski(sK284,k3_relat_1(sK283))
    | r2_hidden(sK286(sK283,sK284),sK284)
    | o_0_0_xboole_0 = sK284 ),
    inference(instantiation,[status(thm)],[c_21680])).

cnf(c_102980,plain,
    ( o_0_0_xboole_0 = sK284
    | r1_tarski(sK284,k3_relat_1(sK283)) != iProver_top
    | r2_hidden(sK286(sK283,sK284),sK284) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_102979])).

cnf(c_103042,plain,
    ( sK284 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_103039,c_1938,c_1925,c_102980])).

cnf(c_103049,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_103042,c_1925])).

cnf(c_103050,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_103049])).

%------------------------------------------------------------------------------
