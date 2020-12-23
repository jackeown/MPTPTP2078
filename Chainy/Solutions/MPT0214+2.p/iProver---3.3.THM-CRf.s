%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0214+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:27 EST 2020

% Result     : Theorem 9.76s
% Output     : CNFRefutation 9.76s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 104 expanded)
%              Number of clauses        :   33 (  33 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :  209 ( 275 expanded)
%              Number of equality atoms :  112 ( 152 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f293,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f292])).

fof(f410,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f293])).

fof(f519,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK28 != sK29
      & r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) ) ),
    introduced(choice_axiom,[])).

fof(f520,plain,
    ( sK28 != sK29
    & r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28,sK29])],[f410,f519])).

fof(f906,plain,(
    r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(cnf_transformation,[],[f520])).

fof(f289,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f517,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f289])).

fof(f518,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f517])).

fof(f901,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f518])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f528,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1160,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | o_0_0_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(definition_unfolding,[],[f901,f528])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f482,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f483,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f482])).

fof(f484,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK20(X0,X1) != X0
          | ~ r2_hidden(sK20(X0,X1),X1) )
        & ( sK20(X0,X1) = X0
          | r2_hidden(sK20(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f485,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK20(X0,X1) != X0
            | ~ r2_hidden(sK20(X0,X1),X1) )
          & ( sK20(X0,X1) = X0
            | r2_hidden(sK20(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f483,f484])).

fof(f753,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f485])).

fof(f1184,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f753])).

fof(f1185,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1184])).

fof(f752,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f485])).

fof(f1186,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f752])).

fof(f288,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f900,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f288])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f476,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f722,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f476])).

fof(f723,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f476])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f718,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f736,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f676,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f908,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f736,f676])).

fof(f1043,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f718,f908])).

fof(f141,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f384,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f141])).

fof(f385,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f384])).

fof(f710,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f385])).

fof(f1037,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ) ),
    inference(definition_unfolding,[],[f710,f908])).

fof(f135,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f376,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f135])).

fof(f377,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f376])).

fof(f702,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f377])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f371,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f698,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f371])).

fof(f1028,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(definition_unfolding,[],[f698,f528])).

fof(f1176,plain,(
    r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f1028])).

fof(f907,plain,(
    sK28 != sK29 ),
    inference(cnf_transformation,[],[f520])).

cnf(c_374,negated_conjecture,
    ( r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) ),
    inference(cnf_transformation,[],[f906])).

cnf(c_11566,plain,
    ( r1_tarski(k1_tarski(sK28),k1_tarski(sK29)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_370,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1160])).

cnf(c_11567,plain,
    ( k1_tarski(X0) = X1
    | o_0_0_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_14317,plain,
    ( k1_tarski(sK29) = k1_tarski(sK28)
    | k1_tarski(sK28) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_11566,c_11567])).

cnf(c_231,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1185])).

cnf(c_11621,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_14975,plain,
    ( k1_tarski(sK28) = o_0_0_xboole_0
    | r2_hidden(sK29,k1_tarski(sK28)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14317,c_11621])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f1186])).

cnf(c_11620,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_232])).

cnf(c_18884,plain,
    ( k1_tarski(sK28) = o_0_0_xboole_0
    | sK29 = sK28 ),
    inference(superposition,[status(thm)],[c_14975,c_11620])).

cnf(c_367,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f900])).

cnf(c_11570,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_19052,plain,
    ( sK29 = sK28
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18884,c_11570])).

cnf(c_201,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f722])).

cnf(c_596,plain,
    ( ~ r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_200,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f723])).

cnf(c_598,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_600,plain,
    ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_196,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(cnf_transformation,[],[f1043])).

cnf(c_608,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_196])).

cnf(c_610,plain,
    ( r1_tarski(o_0_0_xboole_0,k5_xboole_0(k5_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),k4_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_188,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(cnf_transformation,[],[f1037])).

cnf(c_632,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_634,plain,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_tarski(o_0_0_xboole_0,k5_xboole_0(k5_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),k4_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)))) != iProver_top
    | r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_180,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f702])).

cnf(c_648,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_650,plain,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_648])).

cnf(c_177,plain,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1176])).

cnf(c_19892,plain,
    ( sK29 = sK28 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19052,c_596,c_600,c_610,c_634,c_650,c_177])).

cnf(c_373,negated_conjecture,
    ( sK28 != sK29 ),
    inference(cnf_transformation,[],[f907])).

cnf(c_19912,plain,
    ( sK28 != sK28 ),
    inference(demodulation,[status(thm)],[c_19892,c_373])).

cnf(c_19913,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_19912])).

%------------------------------------------------------------------------------
