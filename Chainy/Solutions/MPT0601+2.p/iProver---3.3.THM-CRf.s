%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0601+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:47 EST 2020

% Result     : Theorem 42.45s
% Output     : CNFRefutation 42.45s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 163 expanded)
%              Number of clauses        :   40 (  42 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  263 ( 481 expanded)
%              Number of equality atoms :   76 ( 156 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f973,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f2241,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f973])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1984,plain,(
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
    inference(nnf_transformation,[],[f652])).

fof(f1985,plain,(
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
    inference(rectify,[],[f1984])).

fof(f1988,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1987,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK145(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1986,plain,(
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

fof(f1989,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK144,sK145,sK146])],[f1985,f1988,f1987,f1986])).

fof(f3101,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1989])).

fof(f4128,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f3101])).

fof(f800,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1489,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f800])).

fof(f2028,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1489])).

fof(f3277,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2028])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1610,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f1611,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f1610])).

fof(f2079,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1611])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2178,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2052,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3457,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2178,f2052])).

fof(f3278,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2028])).

fof(f3100,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1989])).

fof(f4129,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK146(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f3100])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f894,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f1629,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK22(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1630,plain,(
    ! [X0] :
      ( r2_hidden(sK22(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f894,f1629])).

fof(f2110,plain,(
    ! [X0] :
      ( r2_hidden(sK22(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1630])).

fof(f3408,plain,(
    ! [X0] :
      ( r2_hidden(sK22(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f2110,f2052])).

fof(f128,axiom,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2218,plain,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f128])).

fof(f3486,plain,(
    ! [X0] : ~ r2_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2218,f2052])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2803,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2740,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f3377,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f2740,f2052])).

fof(f3794,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2803,f3377])).

fof(f592,axiom,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2995,plain,(
    ! [X0] : r1_setfam_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f592])).

fof(f3846,plain,(
    ! [X0] : r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2995,f2052])).

fof(f593,axiom,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1248,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f593])).

fof(f2996,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f1248])).

fof(f3847,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ r1_setfam_1(X0,o_0_0_xboole_0) ) ),
    inference(definition_unfolding,[],[f2996,f2052,f2052])).

fof(f801,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f802,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f801])).

fof(f1490,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f802])).

fof(f2029,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1490])).

fof(f2030,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f2029])).

fof(f2031,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK163,sK162)
        | ~ r2_hidden(sK162,k1_relat_1(sK163)) )
      & ( k1_xboole_0 != k11_relat_1(sK163,sK162)
        | r2_hidden(sK162,k1_relat_1(sK163)) )
      & v1_relat_1(sK163) ) ),
    introduced(choice_axiom,[])).

fof(f2032,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK163,sK162)
      | ~ r2_hidden(sK162,k1_relat_1(sK163)) )
    & ( k1_xboole_0 != k11_relat_1(sK163,sK162)
      | r2_hidden(sK162,k1_relat_1(sK163)) )
    & v1_relat_1(sK163) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK162,sK163])],[f2030,f2031])).

fof(f3281,plain,
    ( k1_xboole_0 = k11_relat_1(sK163,sK162)
    | ~ r2_hidden(sK162,k1_relat_1(sK163)) ),
    inference(cnf_transformation,[],[f2032])).

fof(f3919,plain,
    ( o_0_0_xboole_0 = k11_relat_1(sK163,sK162)
    | ~ r2_hidden(sK162,k1_relat_1(sK163)) ),
    inference(definition_unfolding,[],[f3281,f2052])).

fof(f3280,plain,
    ( k1_xboole_0 != k11_relat_1(sK163,sK162)
    | r2_hidden(sK162,k1_relat_1(sK163)) ),
    inference(cnf_transformation,[],[f2032])).

fof(f3920,plain,
    ( o_0_0_xboole_0 != k11_relat_1(sK163,sK162)
    | r2_hidden(sK162,k1_relat_1(sK163)) ),
    inference(definition_unfolding,[],[f3280,f2052])).

fof(f3279,plain,(
    v1_relat_1(sK163) ),
    inference(cnf_transformation,[],[f2032])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f2241])).

cnf(c_142003,plain,
    ( ~ r2_hidden(sK146(sK163,sK162),k11_relat_1(sK163,sK162))
    | ~ v1_xboole_0(k11_relat_1(sK163,sK162)) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_1043,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4128])).

cnf(c_121406,plain,
    ( ~ r2_hidden(k4_tarski(sK162,sK22(k11_relat_1(sK163,sK162))),sK163)
    | r2_hidden(sK162,k1_relat_1(sK163)) ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_121407,plain,
    ( r2_hidden(k4_tarski(sK162,sK22(k11_relat_1(sK163,sK162))),sK163) != iProver_top
    | r2_hidden(sK162,k1_relat_1(sK163)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_121406])).

cnf(c_1219,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3277])).

cnf(c_98838,plain,
    ( r2_hidden(sK146(sK163,sK162),k11_relat_1(sK163,sK162))
    | ~ r2_hidden(k4_tarski(sK162,sK146(sK163,sK162)),sK163)
    | ~ v1_relat_1(sK163) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_33,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f2079])).

cnf(c_92371,plain,
    ( ~ r1_tarski(X0,k11_relat_1(sK163,sK162))
    | r2_xboole_0(X0,k11_relat_1(sK163,sK162))
    | k11_relat_1(sK163,sK162) = X0 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_92388,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k11_relat_1(sK163,sK162))
    | r2_xboole_0(o_0_0_xboole_0,k11_relat_1(sK163,sK162))
    | k11_relat_1(sK163,sK162) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_92371])).

cnf(c_133,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3457])).

cnf(c_90147,plain,
    ( r1_tarski(o_0_0_xboole_0,k11_relat_1(sK163,sK162)) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_1218,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f3278])).

cnf(c_89422,plain,
    ( r2_hidden(k4_tarski(sK162,sK22(k11_relat_1(sK163,sK162))),sK163)
    | ~ r2_hidden(sK22(k11_relat_1(sK163,sK162)),k11_relat_1(sK163,sK162))
    | ~ v1_relat_1(sK163) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_89423,plain,
    ( r2_hidden(k4_tarski(sK162,sK22(k11_relat_1(sK163,sK162))),sK163) = iProver_top
    | r2_hidden(sK22(k11_relat_1(sK163,sK162)),k11_relat_1(sK163,sK162)) != iProver_top
    | v1_relat_1(sK163) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_89422])).

cnf(c_34355,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_89093,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k11_relat_1(sK163,sK162))
    | k11_relat_1(sK163,sK162) != X0 ),
    inference(instantiation,[status(thm)],[c_34355])).

cnf(c_89095,plain,
    ( v1_xboole_0(k11_relat_1(sK163,sK162))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k11_relat_1(sK163,sK162) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_89093])).

cnf(c_34354,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_89030,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(o_0_0_xboole_0,k11_relat_1(sK163,sK162))
    | X1 != k11_relat_1(sK163,sK162)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_34354])).

cnf(c_89041,plain,
    ( ~ r2_xboole_0(o_0_0_xboole_0,k11_relat_1(sK163,sK162))
    | r2_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 != k11_relat_1(sK163,sK162)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_89030])).

cnf(c_1044,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK146(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f4129])).

cnf(c_71191,plain,
    ( r2_hidden(k4_tarski(sK162,sK146(sK163,sK162)),sK163)
    | ~ r2_hidden(sK162,k1_relat_1(sK163)) ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_66,plain,
    ( r2_hidden(sK22(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3408])).

cnf(c_62776,plain,
    ( r2_hidden(sK22(k11_relat_1(sK163,sK162)),k11_relat_1(sK163,sK162))
    | o_0_0_xboole_0 = k11_relat_1(sK163,sK162) ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_62777,plain,
    ( o_0_0_xboole_0 = k11_relat_1(sK163,sK162)
    | r2_hidden(sK22(k11_relat_1(sK163,sK162)),k11_relat_1(sK163,sK162)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62776])).

cnf(c_172,plain,
    ( ~ r2_xboole_0(X0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3486])).

cnf(c_3710,plain,
    ( ~ r2_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_745,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3794])).

cnf(c_936,plain,
    ( r1_setfam_1(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3846])).

cnf(c_2246,plain,
    ( r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_937,plain,
    ( ~ r1_setfam_1(X0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3847])).

cnf(c_2243,plain,
    ( ~ r1_setfam_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_937])).

cnf(c_1220,negated_conjecture,
    ( ~ r2_hidden(sK162,k1_relat_1(sK163))
    | o_0_0_xboole_0 = k11_relat_1(sK163,sK162) ),
    inference(cnf_transformation,[],[f3919])).

cnf(c_1310,plain,
    ( o_0_0_xboole_0 = k11_relat_1(sK163,sK162)
    | r2_hidden(sK162,k1_relat_1(sK163)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1220])).

cnf(c_1221,negated_conjecture,
    ( r2_hidden(sK162,k1_relat_1(sK163))
    | o_0_0_xboole_0 != k11_relat_1(sK163,sK162) ),
    inference(cnf_transformation,[],[f3920])).

cnf(c_1309,plain,
    ( o_0_0_xboole_0 != k11_relat_1(sK163,sK162)
    | r2_hidden(sK162,k1_relat_1(sK163)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1221])).

cnf(c_1222,negated_conjecture,
    ( v1_relat_1(sK163) ),
    inference(cnf_transformation,[],[f3279])).

cnf(c_1308,plain,
    ( v1_relat_1(sK163) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1222])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_142003,c_121407,c_98838,c_92388,c_90147,c_89423,c_89095,c_89041,c_71191,c_62777,c_3710,c_745,c_2246,c_2243,c_1310,c_1309,c_1221,c_1308,c_1222])).

%------------------------------------------------------------------------------
