%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:47 EST 2020

% Result     : Theorem 47.22s
% Output     : CNFRefutation 47.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 156 expanded)
%              Number of clauses        :   61 (  81 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  206 ( 404 expanded)
%              Number of equality atoms :  129 ( 233 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f17])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21])).

fof(f36,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_179620,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | ~ r1_xboole_0(X1,X2)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_214,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | sK0 != X2
    | sK2 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_215,plain,
    ( ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(X0,sK2)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_177270,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK1),sK0)
    | ~ r1_tarski(k4_xboole_0(sK2,sK1),sK2)
    | k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_245,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_173341,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_246,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_171342,plain,
    ( k4_xboole_0(sK2,sK1) != X0
    | k4_xboole_0(sK2,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_173340,plain,
    ( k4_xboole_0(sK2,sK1) != k4_xboole_0(sK2,sK1)
    | k4_xboole_0(sK2,sK1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_171342])).

cnf(c_172286,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_171145,plain,
    ( r1_tarski(sK2,sK1)
    | k4_xboole_0(sK2,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_170605,plain,
    ( r1_tarski(sK1,sK2)
    | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1022,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_14017,plain,
    ( X0 != k2_xboole_0(X1,sK2)
    | sK2 = X0
    | sK2 != k2_xboole_0(X1,sK2) ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_70945,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | sK2 = sK1
    | sK1 != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_14017])).

cnf(c_620,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_5278,plain,
    ( X0 != k2_xboole_0(X1,X2)
    | sK1 = X0
    | sK1 != k2_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_9944,plain,
    ( X0 != k2_xboole_0(X1,sK1)
    | sK1 = X0
    | sK1 != k2_xboole_0(X1,sK1) ),
    inference(instantiation,[status(thm)],[c_5278])).

cnf(c_23478,plain,
    ( k2_xboole_0(sK1,X0) != k2_xboole_0(X0,sK1)
    | sK1 != k2_xboole_0(X0,sK1)
    | sK1 = k2_xboole_0(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_9944])).

cnf(c_70943,plain,
    ( k2_xboole_0(sK1,sK2) != k2_xboole_0(sK2,sK1)
    | sK1 != k2_xboole_0(sK2,sK1)
    | sK1 = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_23478])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2666,plain,
    ( ~ r1_tarski(X0,sK1)
    | k2_xboole_0(X0,sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_69152,plain,
    ( ~ r1_tarski(sK2,sK1)
    | k2_xboole_0(sK2,sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_2666])).

cnf(c_2636,plain,
    ( ~ r1_tarski(X0,sK2)
    | k2_xboole_0(X0,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_51972,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k2_xboole_0(sK1,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_2636])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_491,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_819,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_491])).

cnf(c_1093,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_819])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_492,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2121,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_492])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_199,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | sK3 != X1
    | sK1 != X2
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(X0,sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_489,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_43022,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0
    | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2121,c_489])).

cnf(c_43023,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_43022])).

cnf(c_728,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_2667,plain,
    ( k2_xboole_0(X0,sK1) != sK1
    | sK1 = k2_xboole_0(X0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_728])).

cnf(c_22741,plain,
    ( k2_xboole_0(sK2,sK1) != sK1
    | sK1 = k2_xboole_0(sK2,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2667])).

cnf(c_22689,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2740,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_7568,plain,
    ( k2_xboole_0(X0,sK2) != sK2
    | sK2 = k2_xboole_0(X0,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2740])).

cnf(c_20648,plain,
    ( k2_xboole_0(sK1,sK2) != sK2
    | sK2 = k2_xboole_0(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_7568])).

cnf(c_2125,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_492])).

cnf(c_3218,plain,
    ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_2125])).

cnf(c_3834,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_491,c_3218])).

cnf(c_3850,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3834])).

cnf(c_801,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_619,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_587,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_618,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_11,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_179620,c_177270,c_173341,c_173340,c_172286,c_171145,c_170605,c_70945,c_70943,c_69152,c_51972,c_43023,c_22741,c_22689,c_20648,c_3850,c_801,c_619,c_618,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:16:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.33  % Running in FOF mode
% 47.22/6.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.22/6.49  
% 47.22/6.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.22/6.49  
% 47.22/6.49  ------  iProver source info
% 47.22/6.49  
% 47.22/6.49  git: date: 2020-06-30 10:37:57 +0100
% 47.22/6.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.22/6.49  git: non_committed_changes: false
% 47.22/6.49  git: last_make_outside_of_git: false
% 47.22/6.49  
% 47.22/6.49  ------ 
% 47.22/6.49  ------ Parsing...
% 47.22/6.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.22/6.49  
% 47.22/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 47.22/6.49  
% 47.22/6.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.22/6.49  
% 47.22/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.22/6.49  ------ Proving...
% 47.22/6.49  ------ Problem Properties 
% 47.22/6.49  
% 47.22/6.49  
% 47.22/6.49  clauses                                 15
% 47.22/6.49  conjectures                             2
% 47.22/6.49  EPR                                     3
% 47.22/6.49  Horn                                    15
% 47.22/6.49  unary                                   8
% 47.22/6.49  binary                                  4
% 47.22/6.49  lits                                    26
% 47.22/6.49  lits eq                                 13
% 47.22/6.49  fd_pure                                 0
% 47.22/6.49  fd_pseudo                               0
% 47.22/6.49  fd_cond                                 3
% 47.22/6.49  fd_pseudo_cond                          0
% 47.22/6.49  AC symbols                              0
% 47.22/6.49  
% 47.22/6.49  ------ Input Options Time Limit: Unbounded
% 47.22/6.49  
% 47.22/6.49  
% 47.22/6.49  ------ 
% 47.22/6.49  Current options:
% 47.22/6.49  ------ 
% 47.22/6.49  
% 47.22/6.49  
% 47.22/6.49  
% 47.22/6.49  
% 47.22/6.49  ------ Proving...
% 47.22/6.49  
% 47.22/6.49  
% 47.22/6.49  % SZS status Theorem for theBenchmark.p
% 47.22/6.49  
% 47.22/6.49  % SZS output start CNFRefutation for theBenchmark.p
% 47.22/6.49  
% 47.22/6.49  fof(f6,axiom,(
% 47.22/6.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 47.22/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.22/6.49  
% 47.22/6.49  fof(f30,plain,(
% 47.22/6.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 47.22/6.49    inference(cnf_transformation,[],[f6])).
% 47.22/6.49  
% 47.22/6.49  fof(f9,axiom,(
% 47.22/6.49    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 47.22/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.22/6.49  
% 47.22/6.49  fof(f15,plain,(
% 47.22/6.49    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 47.22/6.49    inference(ennf_transformation,[],[f9])).
% 47.22/6.49  
% 47.22/6.49  fof(f16,plain,(
% 47.22/6.49    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 47.22/6.49    inference(flattening,[],[f15])).
% 47.22/6.49  
% 47.22/6.49  fof(f33,plain,(
% 47.22/6.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 47.22/6.49    inference(cnf_transformation,[],[f16])).
% 47.22/6.49  
% 47.22/6.49  fof(f11,conjecture,(
% 47.22/6.49    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 47.22/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.22/6.49  
% 47.22/6.49  fof(f12,negated_conjecture,(
% 47.22/6.49    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 47.22/6.49    inference(negated_conjecture,[],[f11])).
% 47.22/6.49  
% 47.22/6.49  fof(f17,plain,(
% 47.22/6.49    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 47.22/6.49    inference(ennf_transformation,[],[f12])).
% 47.22/6.49  
% 47.22/6.49  fof(f18,plain,(
% 47.22/6.49    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 47.22/6.49    inference(flattening,[],[f17])).
% 47.22/6.49  
% 47.22/6.49  fof(f21,plain,(
% 47.22/6.49    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 47.22/6.49    introduced(choice_axiom,[])).
% 47.22/6.49  
% 47.22/6.49  fof(f22,plain,(
% 47.22/6.49    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 47.22/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21])).
% 47.22/6.49  
% 47.22/6.49  fof(f36,plain,(
% 47.22/6.49    r1_xboole_0(sK2,sK0)),
% 47.22/6.49    inference(cnf_transformation,[],[f22])).
% 47.22/6.49  
% 47.22/6.49  fof(f4,axiom,(
% 47.22/6.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 47.22/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.22/6.49  
% 47.22/6.49  fof(f20,plain,(
% 47.22/6.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 47.22/6.49    inference(nnf_transformation,[],[f4])).
% 47.22/6.49  
% 47.22/6.49  fof(f27,plain,(
% 47.22/6.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 47.22/6.49    inference(cnf_transformation,[],[f20])).
% 47.22/6.49  
% 47.22/6.49  fof(f5,axiom,(
% 47.22/6.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 47.22/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.22/6.49  
% 47.22/6.49  fof(f13,plain,(
% 47.22/6.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 47.22/6.49    inference(ennf_transformation,[],[f5])).
% 47.22/6.49  
% 47.22/6.49  fof(f29,plain,(
% 47.22/6.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 47.22/6.49    inference(cnf_transformation,[],[f13])).
% 47.22/6.49  
% 47.22/6.49  fof(f35,plain,(
% 47.22/6.49    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 47.22/6.49    inference(cnf_transformation,[],[f22])).
% 47.22/6.49  
% 47.22/6.49  fof(f1,axiom,(
% 47.22/6.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 47.22/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.22/6.49  
% 47.22/6.49  fof(f23,plain,(
% 47.22/6.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 47.22/6.49    inference(cnf_transformation,[],[f1])).
% 47.22/6.49  
% 47.22/6.49  fof(f10,axiom,(
% 47.22/6.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 47.22/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.22/6.49  
% 47.22/6.49  fof(f34,plain,(
% 47.22/6.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 47.22/6.49    inference(cnf_transformation,[],[f10])).
% 47.22/6.49  
% 47.22/6.49  fof(f7,axiom,(
% 47.22/6.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 47.22/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.22/6.49  
% 47.22/6.49  fof(f14,plain,(
% 47.22/6.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 47.22/6.49    inference(ennf_transformation,[],[f7])).
% 47.22/6.49  
% 47.22/6.49  fof(f31,plain,(
% 47.22/6.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 47.22/6.49    inference(cnf_transformation,[],[f14])).
% 47.22/6.49  
% 47.22/6.49  fof(f37,plain,(
% 47.22/6.49    r1_xboole_0(sK3,sK1)),
% 47.22/6.49    inference(cnf_transformation,[],[f22])).
% 47.22/6.49  
% 47.22/6.49  fof(f38,plain,(
% 47.22/6.49    sK1 != sK2),
% 47.22/6.49    inference(cnf_transformation,[],[f22])).
% 47.22/6.49  
% 47.22/6.49  cnf(c_7,plain,
% 47.22/6.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 47.22/6.49      inference(cnf_transformation,[],[f30]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_179620,plain,
% 47.22/6.49      ( r1_tarski(k4_xboole_0(sK2,sK1),sK2) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_7]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_9,plain,
% 47.22/6.49      ( ~ r1_tarski(X0,X1)
% 47.22/6.49      | ~ r1_tarski(X0,X2)
% 47.22/6.49      | ~ r1_xboole_0(X1,X2)
% 47.22/6.49      | k1_xboole_0 = X0 ),
% 47.22/6.49      inference(cnf_transformation,[],[f33]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_13,negated_conjecture,
% 47.22/6.49      ( r1_xboole_0(sK2,sK0) ),
% 47.22/6.49      inference(cnf_transformation,[],[f36]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_214,plain,
% 47.22/6.49      ( ~ r1_tarski(X0,X1)
% 47.22/6.49      | ~ r1_tarski(X0,X2)
% 47.22/6.49      | sK0 != X2
% 47.22/6.49      | sK2 != X1
% 47.22/6.49      | k1_xboole_0 = X0 ),
% 47.22/6.49      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_215,plain,
% 47.22/6.49      ( ~ r1_tarski(X0,sK0) | ~ r1_tarski(X0,sK2) | k1_xboole_0 = X0 ),
% 47.22/6.49      inference(unflattening,[status(thm)],[c_214]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_177270,plain,
% 47.22/6.49      ( ~ r1_tarski(k4_xboole_0(sK2,sK1),sK0)
% 47.22/6.49      | ~ r1_tarski(k4_xboole_0(sK2,sK1),sK2)
% 47.22/6.49      | k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_215]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_245,plain,( X0 = X0 ),theory(equality) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_173341,plain,
% 47.22/6.49      ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK1) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_245]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_246,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_171342,plain,
% 47.22/6.49      ( k4_xboole_0(sK2,sK1) != X0
% 47.22/6.49      | k4_xboole_0(sK2,sK1) = k1_xboole_0
% 47.22/6.49      | k1_xboole_0 != X0 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_246]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_173340,plain,
% 47.22/6.49      ( k4_xboole_0(sK2,sK1) != k4_xboole_0(sK2,sK1)
% 47.22/6.49      | k4_xboole_0(sK2,sK1) = k1_xboole_0
% 47.22/6.49      | k1_xboole_0 != k4_xboole_0(sK2,sK1) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_171342]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_172286,plain,
% 47.22/6.49      ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_7]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_5,plain,
% 47.22/6.49      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 47.22/6.49      inference(cnf_transformation,[],[f27]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_171145,plain,
% 47.22/6.49      ( r1_tarski(sK2,sK1) | k4_xboole_0(sK2,sK1) != k1_xboole_0 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_5]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_170605,plain,
% 47.22/6.49      ( r1_tarski(sK1,sK2) | k4_xboole_0(sK1,sK2) != k1_xboole_0 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_5]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_1022,plain,
% 47.22/6.49      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_246]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_14017,plain,
% 47.22/6.49      ( X0 != k2_xboole_0(X1,sK2)
% 47.22/6.49      | sK2 = X0
% 47.22/6.49      | sK2 != k2_xboole_0(X1,sK2) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_1022]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_70945,plain,
% 47.22/6.49      ( sK2 != k2_xboole_0(sK1,sK2)
% 47.22/6.49      | sK2 = sK1
% 47.22/6.49      | sK1 != k2_xboole_0(sK1,sK2) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_14017]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_620,plain,
% 47.22/6.49      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_246]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_5278,plain,
% 47.22/6.49      ( X0 != k2_xboole_0(X1,X2) | sK1 = X0 | sK1 != k2_xboole_0(X1,X2) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_620]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_9944,plain,
% 47.22/6.49      ( X0 != k2_xboole_0(X1,sK1)
% 47.22/6.49      | sK1 = X0
% 47.22/6.49      | sK1 != k2_xboole_0(X1,sK1) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_5278]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_23478,plain,
% 47.22/6.49      ( k2_xboole_0(sK1,X0) != k2_xboole_0(X0,sK1)
% 47.22/6.49      | sK1 != k2_xboole_0(X0,sK1)
% 47.22/6.49      | sK1 = k2_xboole_0(sK1,X0) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_9944]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_70943,plain,
% 47.22/6.49      ( k2_xboole_0(sK1,sK2) != k2_xboole_0(sK2,sK1)
% 47.22/6.49      | sK1 != k2_xboole_0(sK2,sK1)
% 47.22/6.49      | sK1 = k2_xboole_0(sK1,sK2) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_23478]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_6,plain,
% 47.22/6.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 47.22/6.49      inference(cnf_transformation,[],[f29]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_2666,plain,
% 47.22/6.49      ( ~ r1_tarski(X0,sK1) | k2_xboole_0(X0,sK1) = sK1 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_6]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_69152,plain,
% 47.22/6.49      ( ~ r1_tarski(sK2,sK1) | k2_xboole_0(sK2,sK1) = sK1 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_2666]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_2636,plain,
% 47.22/6.49      ( ~ r1_tarski(X0,sK2) | k2_xboole_0(X0,sK2) = sK2 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_6]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_51972,plain,
% 47.22/6.49      ( ~ r1_tarski(sK1,sK2) | k2_xboole_0(sK1,sK2) = sK2 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_2636]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_14,negated_conjecture,
% 47.22/6.49      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 47.22/6.49      inference(cnf_transformation,[],[f35]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_0,plain,
% 47.22/6.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 47.22/6.49      inference(cnf_transformation,[],[f23]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_10,plain,
% 47.22/6.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 47.22/6.49      inference(cnf_transformation,[],[f34]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_491,plain,
% 47.22/6.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 47.22/6.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_819,plain,
% 47.22/6.49      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 47.22/6.49      inference(superposition,[status(thm)],[c_0,c_491]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_1093,plain,
% 47.22/6.49      ( r1_tarski(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
% 47.22/6.49      inference(superposition,[status(thm)],[c_14,c_819]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_8,plain,
% 47.22/6.49      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 47.22/6.49      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 47.22/6.49      inference(cnf_transformation,[],[f31]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_492,plain,
% 47.22/6.49      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 47.22/6.49      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 47.22/6.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_2121,plain,
% 47.22/6.49      ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
% 47.22/6.49      inference(superposition,[status(thm)],[c_1093,c_492]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_12,negated_conjecture,
% 47.22/6.49      ( r1_xboole_0(sK3,sK1) ),
% 47.22/6.49      inference(cnf_transformation,[],[f37]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_199,plain,
% 47.22/6.49      ( ~ r1_tarski(X0,X1)
% 47.22/6.49      | ~ r1_tarski(X0,X2)
% 47.22/6.49      | sK3 != X1
% 47.22/6.49      | sK1 != X2
% 47.22/6.49      | k1_xboole_0 = X0 ),
% 47.22/6.49      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_200,plain,
% 47.22/6.49      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(X0,sK1) | k1_xboole_0 = X0 ),
% 47.22/6.49      inference(unflattening,[status(thm)],[c_199]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_489,plain,
% 47.22/6.49      ( k1_xboole_0 = X0
% 47.22/6.49      | r1_tarski(X0,sK3) != iProver_top
% 47.22/6.49      | r1_tarski(X0,sK1) != iProver_top ),
% 47.22/6.49      inference(predicate_to_equality,[status(thm)],[c_200]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_43022,plain,
% 47.22/6.49      ( k4_xboole_0(sK1,sK2) = k1_xboole_0
% 47.22/6.49      | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top ),
% 47.22/6.49      inference(superposition,[status(thm)],[c_2121,c_489]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_43023,plain,
% 47.22/6.49      ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
% 47.22/6.49      | k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 47.22/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_43022]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_728,plain,
% 47.22/6.49      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_620]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_2667,plain,
% 47.22/6.49      ( k2_xboole_0(X0,sK1) != sK1
% 47.22/6.49      | sK1 = k2_xboole_0(X0,sK1)
% 47.22/6.49      | sK1 != sK1 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_728]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_22741,plain,
% 47.22/6.49      ( k2_xboole_0(sK2,sK1) != sK1
% 47.22/6.49      | sK1 = k2_xboole_0(sK2,sK1)
% 47.22/6.49      | sK1 != sK1 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_2667]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_22689,plain,
% 47.22/6.49      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_0]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_2740,plain,
% 47.22/6.49      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_1022]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_7568,plain,
% 47.22/6.49      ( k2_xboole_0(X0,sK2) != sK2
% 47.22/6.49      | sK2 = k2_xboole_0(X0,sK2)
% 47.22/6.49      | sK2 != sK2 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_2740]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_20648,plain,
% 47.22/6.49      ( k2_xboole_0(sK1,sK2) != sK2
% 47.22/6.49      | sK2 = k2_xboole_0(sK1,sK2)
% 47.22/6.49      | sK2 != sK2 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_7568]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_2125,plain,
% 47.22/6.49      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 47.22/6.49      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 47.22/6.49      inference(superposition,[status(thm)],[c_0,c_492]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_3218,plain,
% 47.22/6.49      ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) != iProver_top
% 47.22/6.49      | r1_tarski(k4_xboole_0(X0,sK1),sK0) = iProver_top ),
% 47.22/6.49      inference(superposition,[status(thm)],[c_14,c_2125]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_3834,plain,
% 47.22/6.49      ( r1_tarski(k4_xboole_0(sK2,sK1),sK0) = iProver_top ),
% 47.22/6.49      inference(superposition,[status(thm)],[c_491,c_3218]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_3850,plain,
% 47.22/6.49      ( r1_tarski(k4_xboole_0(sK2,sK1),sK0) ),
% 47.22/6.49      inference(predicate_to_equality_rev,[status(thm)],[c_3834]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_801,plain,
% 47.22/6.49      ( sK2 = sK2 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_245]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_619,plain,
% 47.22/6.49      ( sK1 = sK1 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_245]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_587,plain,
% 47.22/6.49      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_246]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_618,plain,
% 47.22/6.49      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 47.22/6.49      inference(instantiation,[status(thm)],[c_587]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(c_11,negated_conjecture,
% 47.22/6.49      ( sK1 != sK2 ),
% 47.22/6.49      inference(cnf_transformation,[],[f38]) ).
% 47.22/6.49  
% 47.22/6.49  cnf(contradiction,plain,
% 47.22/6.49      ( $false ),
% 47.22/6.49      inference(minisat,
% 47.22/6.49                [status(thm)],
% 47.22/6.49                [c_179620,c_177270,c_173341,c_173340,c_172286,c_171145,
% 47.22/6.49                 c_170605,c_70945,c_70943,c_69152,c_51972,c_43023,
% 47.22/6.49                 c_22741,c_22689,c_20648,c_3850,c_801,c_619,c_618,c_11]) ).
% 47.22/6.49  
% 47.22/6.49  
% 47.22/6.49  % SZS output end CNFRefutation for theBenchmark.p
% 47.22/6.49  
% 47.22/6.49  ------                               Statistics
% 47.22/6.49  
% 47.22/6.49  ------ Selected
% 47.22/6.49  
% 47.22/6.49  total_time:                             5.513
% 47.22/6.49  
%------------------------------------------------------------------------------
