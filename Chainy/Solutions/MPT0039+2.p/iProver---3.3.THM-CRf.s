%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0039+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:14 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 359 expanded)
%              Number of clauses        :   55 ( 104 expanded)
%              Number of leaves         :   14 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          :  299 (1621 expanded)
%              Number of equality atoms :   99 ( 417 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f88])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f135])).

fof(f137,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f136,f137])).

fof(f191,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f66,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f66])).

fof(f123,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f180,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) )
   => ( sK15 != sK16
      & k4_xboole_0(sK15,sK16) = k4_xboole_0(sK16,sK15) ) ),
    introduced(choice_axiom,[])).

fof(f181,plain,
    ( sK15 != sK16
    & k4_xboole_0(sK15,sK16) = k4_xboole_0(sK16,sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f123,f180])).

fof(f281,plain,(
    k4_xboole_0(sK15,sK16) = k4_xboole_0(sK16,sK15) ),
    inference(cnf_transformation,[],[f181])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f149,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f150,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f149])).

fof(f151,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f150])).

fof(f152,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f153,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f151,f152])).

fof(f205,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f153])).

fof(f325,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f205])).

fof(f206,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f153])).

fof(f324,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f206])).

fof(f69,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f124,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f284,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f189,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f314,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f284,f189,f189])).

fof(f207,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f153])).

fof(f323,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f207])).

fof(f192,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f85])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f89])).

fof(f214,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f282,plain,(
    sK15 != sK16 ),
    inference(cnf_transformation,[],[f181])).

fof(f75,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f290,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f126])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f131,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f132,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f131])).

fof(f133,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f134,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f132,f133])).

fof(f188,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f134])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f191])).

cnf(c_30583,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_98,negated_conjecture,
    ( k4_xboole_0(sK15,sK16) = k4_xboole_0(sK16,sK15) ),
    inference(cnf_transformation,[],[f281])).

cnf(c_27,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f325])).

cnf(c_30578,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31149,plain,
    ( r2_hidden(X0,k4_xboole_0(sK15,sK16)) != iProver_top
    | r2_hidden(X0,sK16) = iProver_top ),
    inference(superposition,[status(thm)],[c_98,c_30578])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f324])).

cnf(c_19062,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23306,plain,
    ( r2_hidden(X0,k4_xboole_0(sK15,sK16)) != iProver_top
    | r2_hidden(X0,sK15) != iProver_top ),
    inference(superposition,[status(thm)],[c_98,c_19062])).

cnf(c_19061,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23707,plain,
    ( r2_hidden(X0,k4_xboole_0(sK15,sK16)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23306,c_19061])).

cnf(c_31492,plain,
    ( r2_hidden(X0,k4_xboole_0(sK15,sK16)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31149,c_23707])).

cnf(c_31498,plain,
    ( r1_tarski(k4_xboole_0(sK15,sK16),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_30583,c_31492])).

cnf(c_100,plain,
    ( ~ r1_tarski(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f314])).

cnf(c_30571,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(X0,o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100])).

cnf(c_31657,plain,
    ( k4_xboole_0(sK15,sK16) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_31498,c_30571])).

cnf(c_31853,plain,
    ( k4_xboole_0(sK16,sK15) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31657,c_98])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f323])).

cnf(c_30580,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_32653,plain,
    ( r2_hidden(X0,sK16) != iProver_top
    | r2_hidden(X0,sK15) = iProver_top
    | r2_hidden(X0,o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_31853,c_30580])).

cnf(c_31852,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31657,c_31492])).

cnf(c_32885,plain,
    ( r2_hidden(X0,sK15) = iProver_top
    | r2_hidden(X0,sK16) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32653,c_31852])).

cnf(c_32886,plain,
    ( r2_hidden(X0,sK16) != iProver_top
    | r2_hidden(X0,sK15) = iProver_top ),
    inference(renaming,[status(thm)],[c_32885])).

cnf(c_32894,plain,
    ( r1_tarski(sK16,X0) = iProver_top
    | r2_hidden(sK1(sK16,X0),sK15) = iProver_top ),
    inference(superposition,[status(thm)],[c_30583,c_32886])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f192])).

cnf(c_30584,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_33067,plain,
    ( r1_tarski(sK16,sK15) = iProver_top ),
    inference(superposition,[status(thm)],[c_32894,c_30584])).

cnf(c_30,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f214])).

cnf(c_97,negated_conjecture,
    ( sK15 != sK16 ),
    inference(cnf_transformation,[],[f282])).

cnf(c_28249,plain,
    ( ~ r1_tarski(sK15,sK16)
    | r2_xboole_0(sK15,sK16) ),
    inference(resolution,[status(thm)],[c_30,c_97])).

cnf(c_10798,plain,
    ( r1_tarski(sK15,sK16)
    | ~ r2_hidden(sK1(sK15,sK16),sK16) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_10797,plain,
    ( r1_tarski(sK15,sK16)
    | r2_hidden(sK1(sK15,sK16),sK15) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_106,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f290])).

cnf(c_21149,plain,
    ( ~ r2_hidden(sK1(sK15,sK16),k4_xboole_0(sK15,X0))
    | ~ v1_xboole_0(k4_xboole_0(sK15,X0)) ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_23239,plain,
    ( ~ r2_hidden(sK1(sK15,sK16),k4_xboole_0(sK15,sK16))
    | ~ v1_xboole_0(k4_xboole_0(sK15,sK16)) ),
    inference(instantiation,[status(thm)],[c_21149])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f188])).

cnf(c_19068,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_23711,plain,
    ( v1_xboole_0(k4_xboole_0(sK15,sK16)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19068,c_23707])).

cnf(c_23744,plain,
    ( v1_xboole_0(k4_xboole_0(sK15,sK16)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_23711])).

cnf(c_20457,plain,
    ( r2_hidden(sK1(sK15,sK16),X0)
    | r2_hidden(sK1(sK15,sK16),k4_xboole_0(sK15,X0))
    | ~ r2_hidden(sK1(sK15,sK16),sK15) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_24088,plain,
    ( r2_hidden(sK1(sK15,sK16),k4_xboole_0(sK15,sK16))
    | r2_hidden(sK1(sK15,sK16),sK16)
    | ~ r2_hidden(sK1(sK15,sK16),sK15) ),
    inference(instantiation,[status(thm)],[c_20457])).

cnf(c_24357,plain,
    ( ~ r1_tarski(sK15,sK16)
    | r2_xboole_0(sK15,sK16)
    | sK15 = sK16 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_28610,plain,
    ( r2_xboole_0(sK15,sK16) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28249,c_97,c_10798,c_10797,c_23239,c_23744,c_24088,c_24357])).

cnf(c_28612,plain,
    ( r2_xboole_0(sK15,sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28610])).

cnf(c_27398,plain,
    ( ~ r1_tarski(X0,sK15)
    | r2_xboole_0(X0,sK15)
    | X0 = sK15 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_28046,plain,
    ( ~ r1_tarski(sK16,sK15)
    | r2_xboole_0(sK16,sK15)
    | sK16 = sK15 ),
    inference(instantiation,[status(thm)],[c_27398])).

cnf(c_28047,plain,
    ( sK16 = sK15
    | r1_tarski(sK16,sK15) != iProver_top
    | r2_xboole_0(sK16,sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28046])).

cnf(c_1,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f183])).

cnf(c_24386,plain,
    ( ~ r2_xboole_0(sK16,sK15)
    | ~ r2_xboole_0(sK15,sK16) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_24387,plain,
    ( r2_xboole_0(sK16,sK15) != iProver_top
    | r2_xboole_0(sK15,sK16) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24386])).

cnf(c_1441,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4843,plain,
    ( sK16 != X0
    | sK15 != X0
    | sK15 = sK16 ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_4851,plain,
    ( sK16 != sK15
    | sK15 = sK16
    | sK15 != sK15 ),
    inference(instantiation,[status(thm)],[c_4843])).

cnf(c_4852,plain,
    ( sK16 != sK15
    | sK15 = sK16 ),
    inference(equality_resolution_simp,[status(thm)],[c_4851])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33067,c_28612,c_28047,c_24387,c_4852,c_97])).

%------------------------------------------------------------------------------
