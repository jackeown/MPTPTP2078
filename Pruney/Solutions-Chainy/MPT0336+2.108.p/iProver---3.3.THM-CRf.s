%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:51 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 122 expanded)
%              Number of clauses        :   42 (  49 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   16
%              Number of atoms          :  185 ( 335 expanded)
%              Number of equality atoms :   50 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f17])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
      & r1_xboole_0(sK3,sK2)
      & r2_hidden(sK4,sK3)
      & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f23])).

fof(f40,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f19])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_710,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_712,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_728,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1193,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_728])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_715,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_711,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_727,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2838,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_711,c_727])).

cnf(c_3183,plain,
    ( k4_xboole_0(X0,k1_tarski(sK4)) = X0
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_2838])).

cnf(c_3335,plain,
    ( k4_xboole_0(sK2,k1_tarski(sK4)) = sK2 ),
    inference(superposition,[status(thm)],[c_1193,c_3183])).

cnf(c_10,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_718,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1192,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_728])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_716,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1374,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1192,c_716])).

cnf(c_3465,plain,
    ( k4_xboole_0(k1_tarski(sK4),sK2) = k1_tarski(sK4) ),
    inference(superposition,[status(thm)],[c_3335,c_1374])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_724,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3602,plain,
    ( r1_tarski(X0,k1_tarski(sK4)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3465,c_724])).

cnf(c_16927,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_710,c_3602])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_719,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k3_xboole_0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16934,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_16927,c_719])).

cnf(c_17216,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_16934,c_728])).

cnf(c_1163,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1164,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1163])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_927,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
    | ~ r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_928,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_840,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_841,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) = iProver_top
    | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_15,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_21,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17216,c_1164,c_928,c_841,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:49:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.97/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/0.97  
% 3.97/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.97/0.97  
% 3.97/0.97  ------  iProver source info
% 3.97/0.97  
% 3.97/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.97/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.97/0.97  git: non_committed_changes: false
% 3.97/0.97  git: last_make_outside_of_git: false
% 3.97/0.97  
% 3.97/0.97  ------ 
% 3.97/0.97  
% 3.97/0.97  ------ Input Options
% 3.97/0.97  
% 3.97/0.97  --out_options                           all
% 3.97/0.97  --tptp_safe_out                         true
% 3.97/0.97  --problem_path                          ""
% 3.97/0.97  --include_path                          ""
% 3.97/0.97  --clausifier                            res/vclausify_rel
% 3.97/0.97  --clausifier_options                    --mode clausify
% 3.97/0.97  --stdin                                 false
% 3.97/0.97  --stats_out                             all
% 3.97/0.97  
% 3.97/0.97  ------ General Options
% 3.97/0.97  
% 3.97/0.97  --fof                                   false
% 3.97/0.97  --time_out_real                         305.
% 3.97/0.97  --time_out_virtual                      -1.
% 3.97/0.97  --symbol_type_check                     false
% 3.97/0.97  --clausify_out                          false
% 3.97/0.97  --sig_cnt_out                           false
% 3.97/0.97  --trig_cnt_out                          false
% 3.97/0.97  --trig_cnt_out_tolerance                1.
% 3.97/0.97  --trig_cnt_out_sk_spl                   false
% 3.97/0.97  --abstr_cl_out                          false
% 3.97/0.97  
% 3.97/0.97  ------ Global Options
% 3.97/0.97  
% 3.97/0.97  --schedule                              default
% 3.97/0.97  --add_important_lit                     false
% 3.97/0.97  --prop_solver_per_cl                    1000
% 3.97/0.97  --min_unsat_core                        false
% 3.97/0.97  --soft_assumptions                      false
% 3.97/0.97  --soft_lemma_size                       3
% 3.97/0.97  --prop_impl_unit_size                   0
% 3.97/0.97  --prop_impl_unit                        []
% 3.97/0.97  --share_sel_clauses                     true
% 3.97/0.97  --reset_solvers                         false
% 3.97/0.97  --bc_imp_inh                            [conj_cone]
% 3.97/0.97  --conj_cone_tolerance                   3.
% 3.97/0.97  --extra_neg_conj                        none
% 3.97/0.97  --large_theory_mode                     true
% 3.97/0.97  --prolific_symb_bound                   200
% 3.97/0.97  --lt_threshold                          2000
% 3.97/0.97  --clause_weak_htbl                      true
% 3.97/0.97  --gc_record_bc_elim                     false
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing Options
% 3.97/0.97  
% 3.97/0.97  --preprocessing_flag                    true
% 3.97/0.97  --time_out_prep_mult                    0.1
% 3.97/0.97  --splitting_mode                        input
% 3.97/0.97  --splitting_grd                         true
% 3.97/0.97  --splitting_cvd                         false
% 3.97/0.97  --splitting_cvd_svl                     false
% 3.97/0.97  --splitting_nvd                         32
% 3.97/0.97  --sub_typing                            true
% 3.97/0.97  --prep_gs_sim                           true
% 3.97/0.97  --prep_unflatten                        true
% 3.97/0.97  --prep_res_sim                          true
% 3.97/0.97  --prep_upred                            true
% 3.97/0.97  --prep_sem_filter                       exhaustive
% 3.97/0.97  --prep_sem_filter_out                   false
% 3.97/0.97  --pred_elim                             true
% 3.97/0.97  --res_sim_input                         true
% 3.97/0.97  --eq_ax_congr_red                       true
% 3.97/0.97  --pure_diseq_elim                       true
% 3.97/0.97  --brand_transform                       false
% 3.97/0.97  --non_eq_to_eq                          false
% 3.97/0.97  --prep_def_merge                        true
% 3.97/0.97  --prep_def_merge_prop_impl              false
% 3.97/0.97  --prep_def_merge_mbd                    true
% 3.97/0.97  --prep_def_merge_tr_red                 false
% 3.97/0.97  --prep_def_merge_tr_cl                  false
% 3.97/0.97  --smt_preprocessing                     true
% 3.97/0.97  --smt_ac_axioms                         fast
% 3.97/0.97  --preprocessed_out                      false
% 3.97/0.97  --preprocessed_stats                    false
% 3.97/0.97  
% 3.97/0.97  ------ Abstraction refinement Options
% 3.97/0.97  
% 3.97/0.97  --abstr_ref                             []
% 3.97/0.97  --abstr_ref_prep                        false
% 3.97/0.97  --abstr_ref_until_sat                   false
% 3.97/0.97  --abstr_ref_sig_restrict                funpre
% 3.97/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.97  --abstr_ref_under                       []
% 3.97/0.97  
% 3.97/0.97  ------ SAT Options
% 3.97/0.97  
% 3.97/0.97  --sat_mode                              false
% 3.97/0.97  --sat_fm_restart_options                ""
% 3.97/0.97  --sat_gr_def                            false
% 3.97/0.97  --sat_epr_types                         true
% 3.97/0.97  --sat_non_cyclic_types                  false
% 3.97/0.97  --sat_finite_models                     false
% 3.97/0.97  --sat_fm_lemmas                         false
% 3.97/0.97  --sat_fm_prep                           false
% 3.97/0.97  --sat_fm_uc_incr                        true
% 3.97/0.97  --sat_out_model                         small
% 3.97/0.97  --sat_out_clauses                       false
% 3.97/0.97  
% 3.97/0.97  ------ QBF Options
% 3.97/0.97  
% 3.97/0.97  --qbf_mode                              false
% 3.97/0.97  --qbf_elim_univ                         false
% 3.97/0.97  --qbf_dom_inst                          none
% 3.97/0.97  --qbf_dom_pre_inst                      false
% 3.97/0.97  --qbf_sk_in                             false
% 3.97/0.97  --qbf_pred_elim                         true
% 3.97/0.97  --qbf_split                             512
% 3.97/0.97  
% 3.97/0.97  ------ BMC1 Options
% 3.97/0.97  
% 3.97/0.97  --bmc1_incremental                      false
% 3.97/0.97  --bmc1_axioms                           reachable_all
% 3.97/0.97  --bmc1_min_bound                        0
% 3.97/0.97  --bmc1_max_bound                        -1
% 3.97/0.97  --bmc1_max_bound_default                -1
% 3.97/0.97  --bmc1_symbol_reachability              true
% 3.97/0.97  --bmc1_property_lemmas                  false
% 3.97/0.97  --bmc1_k_induction                      false
% 3.97/0.97  --bmc1_non_equiv_states                 false
% 3.97/0.97  --bmc1_deadlock                         false
% 3.97/0.97  --bmc1_ucm                              false
% 3.97/0.97  --bmc1_add_unsat_core                   none
% 3.97/0.97  --bmc1_unsat_core_children              false
% 3.97/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.97  --bmc1_out_stat                         full
% 3.97/0.97  --bmc1_ground_init                      false
% 3.97/0.97  --bmc1_pre_inst_next_state              false
% 3.97/0.97  --bmc1_pre_inst_state                   false
% 3.97/0.97  --bmc1_pre_inst_reach_state             false
% 3.97/0.97  --bmc1_out_unsat_core                   false
% 3.97/0.97  --bmc1_aig_witness_out                  false
% 3.97/0.97  --bmc1_verbose                          false
% 3.97/0.97  --bmc1_dump_clauses_tptp                false
% 3.97/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.97  --bmc1_dump_file                        -
% 3.97/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.97  --bmc1_ucm_extend_mode                  1
% 3.97/0.97  --bmc1_ucm_init_mode                    2
% 3.97/0.97  --bmc1_ucm_cone_mode                    none
% 3.97/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.97  --bmc1_ucm_relax_model                  4
% 3.97/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.97  --bmc1_ucm_layered_model                none
% 3.97/0.97  --bmc1_ucm_max_lemma_size               10
% 3.97/0.97  
% 3.97/0.97  ------ AIG Options
% 3.97/0.97  
% 3.97/0.97  --aig_mode                              false
% 3.97/0.97  
% 3.97/0.97  ------ Instantiation Options
% 3.97/0.97  
% 3.97/0.97  --instantiation_flag                    true
% 3.97/0.97  --inst_sos_flag                         false
% 3.97/0.97  --inst_sos_phase                        true
% 3.97/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel_side                     num_symb
% 3.97/0.97  --inst_solver_per_active                1400
% 3.97/0.97  --inst_solver_calls_frac                1.
% 3.97/0.97  --inst_passive_queue_type               priority_queues
% 3.97/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.97  --inst_passive_queues_freq              [25;2]
% 3.97/0.97  --inst_dismatching                      true
% 3.97/0.97  --inst_eager_unprocessed_to_passive     true
% 3.97/0.97  --inst_prop_sim_given                   true
% 3.97/0.97  --inst_prop_sim_new                     false
% 3.97/0.97  --inst_subs_new                         false
% 3.97/0.97  --inst_eq_res_simp                      false
% 3.97/0.97  --inst_subs_given                       false
% 3.97/0.97  --inst_orphan_elimination               true
% 3.97/0.97  --inst_learning_loop_flag               true
% 3.97/0.97  --inst_learning_start                   3000
% 3.97/0.97  --inst_learning_factor                  2
% 3.97/0.97  --inst_start_prop_sim_after_learn       3
% 3.97/0.97  --inst_sel_renew                        solver
% 3.97/0.97  --inst_lit_activity_flag                true
% 3.97/0.97  --inst_restr_to_given                   false
% 3.97/0.97  --inst_activity_threshold               500
% 3.97/0.97  --inst_out_proof                        true
% 3.97/0.97  
% 3.97/0.97  ------ Resolution Options
% 3.97/0.97  
% 3.97/0.97  --resolution_flag                       true
% 3.97/0.97  --res_lit_sel                           adaptive
% 3.97/0.97  --res_lit_sel_side                      none
% 3.97/0.97  --res_ordering                          kbo
% 3.97/0.97  --res_to_prop_solver                    active
% 3.97/0.97  --res_prop_simpl_new                    false
% 3.97/0.97  --res_prop_simpl_given                  true
% 3.97/0.97  --res_passive_queue_type                priority_queues
% 3.97/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.97  --res_passive_queues_freq               [15;5]
% 3.97/0.97  --res_forward_subs                      full
% 3.97/0.97  --res_backward_subs                     full
% 3.97/0.97  --res_forward_subs_resolution           true
% 3.97/0.97  --res_backward_subs_resolution          true
% 3.97/0.97  --res_orphan_elimination                true
% 3.97/0.97  --res_time_limit                        2.
% 3.97/0.97  --res_out_proof                         true
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Options
% 3.97/0.97  
% 3.97/0.97  --superposition_flag                    true
% 3.97/0.97  --sup_passive_queue_type                priority_queues
% 3.97/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.97/0.97  --demod_completeness_check              fast
% 3.97/0.97  --demod_use_ground                      true
% 3.97/0.97  --sup_to_prop_solver                    passive
% 3.97/0.97  --sup_prop_simpl_new                    true
% 3.97/0.97  --sup_prop_simpl_given                  true
% 3.97/0.97  --sup_fun_splitting                     false
% 3.97/0.97  --sup_smt_interval                      50000
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Simplification Setup
% 3.97/0.97  
% 3.97/0.97  --sup_indices_passive                   []
% 3.97/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_full_bw                           [BwDemod]
% 3.97/0.97  --sup_immed_triv                        [TrivRules]
% 3.97/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_immed_bw_main                     []
% 3.97/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  
% 3.97/0.97  ------ Combination Options
% 3.97/0.97  
% 3.97/0.97  --comb_res_mult                         3
% 3.97/0.97  --comb_sup_mult                         2
% 3.97/0.97  --comb_inst_mult                        10
% 3.97/0.97  
% 3.97/0.97  ------ Debug Options
% 3.97/0.97  
% 3.97/0.97  --dbg_backtrace                         false
% 3.97/0.97  --dbg_dump_prop_clauses                 false
% 3.97/0.97  --dbg_dump_prop_clauses_file            -
% 3.97/0.97  --dbg_out_stat                          false
% 3.97/0.97  ------ Parsing...
% 3.97/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.97/0.97  ------ Proving...
% 3.97/0.97  ------ Problem Properties 
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  clauses                                 19
% 3.97/0.97  conjectures                             4
% 3.97/0.97  EPR                                     4
% 3.97/0.97  Horn                                    16
% 3.97/0.97  unary                                   5
% 3.97/0.97  binary                                  12
% 3.97/0.97  lits                                    35
% 3.97/0.97  lits eq                                 4
% 3.97/0.97  fd_pure                                 0
% 3.97/0.97  fd_pseudo                               0
% 3.97/0.97  fd_cond                                 0
% 3.97/0.97  fd_pseudo_cond                          0
% 3.97/0.97  AC symbols                              0
% 3.97/0.97  
% 3.97/0.97  ------ Schedule dynamic 5 is on 
% 3.97/0.97  
% 3.97/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  ------ 
% 3.97/0.97  Current options:
% 3.97/0.97  ------ 
% 3.97/0.97  
% 3.97/0.97  ------ Input Options
% 3.97/0.97  
% 3.97/0.97  --out_options                           all
% 3.97/0.97  --tptp_safe_out                         true
% 3.97/0.97  --problem_path                          ""
% 3.97/0.97  --include_path                          ""
% 3.97/0.97  --clausifier                            res/vclausify_rel
% 3.97/0.97  --clausifier_options                    --mode clausify
% 3.97/0.97  --stdin                                 false
% 3.97/0.97  --stats_out                             all
% 3.97/0.97  
% 3.97/0.97  ------ General Options
% 3.97/0.97  
% 3.97/0.97  --fof                                   false
% 3.97/0.97  --time_out_real                         305.
% 3.97/0.97  --time_out_virtual                      -1.
% 3.97/0.97  --symbol_type_check                     false
% 3.97/0.97  --clausify_out                          false
% 3.97/0.97  --sig_cnt_out                           false
% 3.97/0.97  --trig_cnt_out                          false
% 3.97/0.97  --trig_cnt_out_tolerance                1.
% 3.97/0.97  --trig_cnt_out_sk_spl                   false
% 3.97/0.97  --abstr_cl_out                          false
% 3.97/0.97  
% 3.97/0.97  ------ Global Options
% 3.97/0.97  
% 3.97/0.97  --schedule                              default
% 3.97/0.97  --add_important_lit                     false
% 3.97/0.97  --prop_solver_per_cl                    1000
% 3.97/0.97  --min_unsat_core                        false
% 3.97/0.97  --soft_assumptions                      false
% 3.97/0.97  --soft_lemma_size                       3
% 3.97/0.97  --prop_impl_unit_size                   0
% 3.97/0.97  --prop_impl_unit                        []
% 3.97/0.97  --share_sel_clauses                     true
% 3.97/0.97  --reset_solvers                         false
% 3.97/0.97  --bc_imp_inh                            [conj_cone]
% 3.97/0.97  --conj_cone_tolerance                   3.
% 3.97/0.97  --extra_neg_conj                        none
% 3.97/0.97  --large_theory_mode                     true
% 3.97/0.97  --prolific_symb_bound                   200
% 3.97/0.97  --lt_threshold                          2000
% 3.97/0.97  --clause_weak_htbl                      true
% 3.97/0.97  --gc_record_bc_elim                     false
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing Options
% 3.97/0.97  
% 3.97/0.97  --preprocessing_flag                    true
% 3.97/0.97  --time_out_prep_mult                    0.1
% 3.97/0.97  --splitting_mode                        input
% 3.97/0.97  --splitting_grd                         true
% 3.97/0.97  --splitting_cvd                         false
% 3.97/0.97  --splitting_cvd_svl                     false
% 3.97/0.97  --splitting_nvd                         32
% 3.97/0.97  --sub_typing                            true
% 3.97/0.97  --prep_gs_sim                           true
% 3.97/0.97  --prep_unflatten                        true
% 3.97/0.97  --prep_res_sim                          true
% 3.97/0.97  --prep_upred                            true
% 3.97/0.97  --prep_sem_filter                       exhaustive
% 3.97/0.97  --prep_sem_filter_out                   false
% 3.97/0.97  --pred_elim                             true
% 3.97/0.97  --res_sim_input                         true
% 3.97/0.97  --eq_ax_congr_red                       true
% 3.97/0.97  --pure_diseq_elim                       true
% 3.97/0.97  --brand_transform                       false
% 3.97/0.97  --non_eq_to_eq                          false
% 3.97/0.97  --prep_def_merge                        true
% 3.97/0.97  --prep_def_merge_prop_impl              false
% 3.97/0.97  --prep_def_merge_mbd                    true
% 3.97/0.97  --prep_def_merge_tr_red                 false
% 3.97/0.97  --prep_def_merge_tr_cl                  false
% 3.97/0.97  --smt_preprocessing                     true
% 3.97/0.97  --smt_ac_axioms                         fast
% 3.97/0.97  --preprocessed_out                      false
% 3.97/0.97  --preprocessed_stats                    false
% 3.97/0.97  
% 3.97/0.97  ------ Abstraction refinement Options
% 3.97/0.97  
% 3.97/0.97  --abstr_ref                             []
% 3.97/0.97  --abstr_ref_prep                        false
% 3.97/0.97  --abstr_ref_until_sat                   false
% 3.97/0.97  --abstr_ref_sig_restrict                funpre
% 3.97/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.97  --abstr_ref_under                       []
% 3.97/0.97  
% 3.97/0.97  ------ SAT Options
% 3.97/0.97  
% 3.97/0.97  --sat_mode                              false
% 3.97/0.97  --sat_fm_restart_options                ""
% 3.97/0.97  --sat_gr_def                            false
% 3.97/0.97  --sat_epr_types                         true
% 3.97/0.97  --sat_non_cyclic_types                  false
% 3.97/0.97  --sat_finite_models                     false
% 3.97/0.97  --sat_fm_lemmas                         false
% 3.97/0.97  --sat_fm_prep                           false
% 3.97/0.97  --sat_fm_uc_incr                        true
% 3.97/0.97  --sat_out_model                         small
% 3.97/0.97  --sat_out_clauses                       false
% 3.97/0.97  
% 3.97/0.97  ------ QBF Options
% 3.97/0.97  
% 3.97/0.97  --qbf_mode                              false
% 3.97/0.97  --qbf_elim_univ                         false
% 3.97/0.97  --qbf_dom_inst                          none
% 3.97/0.97  --qbf_dom_pre_inst                      false
% 3.97/0.97  --qbf_sk_in                             false
% 3.97/0.97  --qbf_pred_elim                         true
% 3.97/0.97  --qbf_split                             512
% 3.97/0.97  
% 3.97/0.97  ------ BMC1 Options
% 3.97/0.97  
% 3.97/0.97  --bmc1_incremental                      false
% 3.97/0.97  --bmc1_axioms                           reachable_all
% 3.97/0.97  --bmc1_min_bound                        0
% 3.97/0.97  --bmc1_max_bound                        -1
% 3.97/0.97  --bmc1_max_bound_default                -1
% 3.97/0.97  --bmc1_symbol_reachability              true
% 3.97/0.97  --bmc1_property_lemmas                  false
% 3.97/0.97  --bmc1_k_induction                      false
% 3.97/0.97  --bmc1_non_equiv_states                 false
% 3.97/0.97  --bmc1_deadlock                         false
% 3.97/0.97  --bmc1_ucm                              false
% 3.97/0.97  --bmc1_add_unsat_core                   none
% 3.97/0.97  --bmc1_unsat_core_children              false
% 3.97/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.97  --bmc1_out_stat                         full
% 3.97/0.97  --bmc1_ground_init                      false
% 3.97/0.97  --bmc1_pre_inst_next_state              false
% 3.97/0.97  --bmc1_pre_inst_state                   false
% 3.97/0.97  --bmc1_pre_inst_reach_state             false
% 3.97/0.97  --bmc1_out_unsat_core                   false
% 3.97/0.97  --bmc1_aig_witness_out                  false
% 3.97/0.97  --bmc1_verbose                          false
% 3.97/0.97  --bmc1_dump_clauses_tptp                false
% 3.97/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.97  --bmc1_dump_file                        -
% 3.97/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.97  --bmc1_ucm_extend_mode                  1
% 3.97/0.97  --bmc1_ucm_init_mode                    2
% 3.97/0.97  --bmc1_ucm_cone_mode                    none
% 3.97/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.97  --bmc1_ucm_relax_model                  4
% 3.97/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.97  --bmc1_ucm_layered_model                none
% 3.97/0.97  --bmc1_ucm_max_lemma_size               10
% 3.97/0.97  
% 3.97/0.97  ------ AIG Options
% 3.97/0.97  
% 3.97/0.97  --aig_mode                              false
% 3.97/0.97  
% 3.97/0.97  ------ Instantiation Options
% 3.97/0.97  
% 3.97/0.97  --instantiation_flag                    true
% 3.97/0.97  --inst_sos_flag                         false
% 3.97/0.97  --inst_sos_phase                        true
% 3.97/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.97  --inst_lit_sel_side                     none
% 3.97/0.97  --inst_solver_per_active                1400
% 3.97/0.97  --inst_solver_calls_frac                1.
% 3.97/0.97  --inst_passive_queue_type               priority_queues
% 3.97/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.97  --inst_passive_queues_freq              [25;2]
% 3.97/0.97  --inst_dismatching                      true
% 3.97/0.97  --inst_eager_unprocessed_to_passive     true
% 3.97/0.97  --inst_prop_sim_given                   true
% 3.97/0.97  --inst_prop_sim_new                     false
% 3.97/0.97  --inst_subs_new                         false
% 3.97/0.97  --inst_eq_res_simp                      false
% 3.97/0.97  --inst_subs_given                       false
% 3.97/0.97  --inst_orphan_elimination               true
% 3.97/0.97  --inst_learning_loop_flag               true
% 3.97/0.97  --inst_learning_start                   3000
% 3.97/0.97  --inst_learning_factor                  2
% 3.97/0.97  --inst_start_prop_sim_after_learn       3
% 3.97/0.97  --inst_sel_renew                        solver
% 3.97/0.97  --inst_lit_activity_flag                true
% 3.97/0.97  --inst_restr_to_given                   false
% 3.97/0.97  --inst_activity_threshold               500
% 3.97/0.97  --inst_out_proof                        true
% 3.97/0.97  
% 3.97/0.97  ------ Resolution Options
% 3.97/0.97  
% 3.97/0.97  --resolution_flag                       false
% 3.97/0.97  --res_lit_sel                           adaptive
% 3.97/0.97  --res_lit_sel_side                      none
% 3.97/0.97  --res_ordering                          kbo
% 3.97/0.97  --res_to_prop_solver                    active
% 3.97/0.97  --res_prop_simpl_new                    false
% 3.97/0.97  --res_prop_simpl_given                  true
% 3.97/0.97  --res_passive_queue_type                priority_queues
% 3.97/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.97  --res_passive_queues_freq               [15;5]
% 3.97/0.97  --res_forward_subs                      full
% 3.97/0.97  --res_backward_subs                     full
% 3.97/0.97  --res_forward_subs_resolution           true
% 3.97/0.97  --res_backward_subs_resolution          true
% 3.97/0.97  --res_orphan_elimination                true
% 3.97/0.97  --res_time_limit                        2.
% 3.97/0.97  --res_out_proof                         true
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Options
% 3.97/0.97  
% 3.97/0.97  --superposition_flag                    true
% 3.97/0.97  --sup_passive_queue_type                priority_queues
% 3.97/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.97/0.97  --demod_completeness_check              fast
% 3.97/0.97  --demod_use_ground                      true
% 3.97/0.97  --sup_to_prop_solver                    passive
% 3.97/0.97  --sup_prop_simpl_new                    true
% 3.97/0.97  --sup_prop_simpl_given                  true
% 3.97/0.97  --sup_fun_splitting                     false
% 3.97/0.97  --sup_smt_interval                      50000
% 3.97/0.97  
% 3.97/0.97  ------ Superposition Simplification Setup
% 3.97/0.97  
% 3.97/0.97  --sup_indices_passive                   []
% 3.97/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_full_bw                           [BwDemod]
% 3.97/0.97  --sup_immed_triv                        [TrivRules]
% 3.97/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_immed_bw_main                     []
% 3.97/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.97  
% 3.97/0.97  ------ Combination Options
% 3.97/0.97  
% 3.97/0.97  --comb_res_mult                         3
% 3.97/0.97  --comb_sup_mult                         2
% 3.97/0.97  --comb_inst_mult                        10
% 3.97/0.97  
% 3.97/0.97  ------ Debug Options
% 3.97/0.97  
% 3.97/0.97  --dbg_backtrace                         false
% 3.97/0.97  --dbg_dump_prop_clauses                 false
% 3.97/0.97  --dbg_dump_prop_clauses_file            -
% 3.97/0.97  --dbg_out_stat                          false
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  ------ Proving...
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  % SZS status Theorem for theBenchmark.p
% 3.97/0.97  
% 3.97/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.97/0.97  
% 3.97/0.97  fof(f9,conjecture,(
% 3.97/0.97    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f10,negated_conjecture,(
% 3.97/0.97    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.97/0.97    inference(negated_conjecture,[],[f9])).
% 3.97/0.97  
% 3.97/0.97  fof(f17,plain,(
% 3.97/0.97    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 3.97/0.97    inference(ennf_transformation,[],[f10])).
% 3.97/0.97  
% 3.97/0.97  fof(f18,plain,(
% 3.97/0.97    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 3.97/0.97    inference(flattening,[],[f17])).
% 3.97/0.97  
% 3.97/0.97  fof(f23,plain,(
% 3.97/0.97    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 3.97/0.97    introduced(choice_axiom,[])).
% 3.97/0.97  
% 3.97/0.97  fof(f24,plain,(
% 3.97/0.97    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 3.97/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f23])).
% 3.97/0.97  
% 3.97/0.97  fof(f40,plain,(
% 3.97/0.97    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 3.97/0.97    inference(cnf_transformation,[],[f24])).
% 3.97/0.97  
% 3.97/0.97  fof(f42,plain,(
% 3.97/0.97    r1_xboole_0(sK3,sK2)),
% 3.97/0.97    inference(cnf_transformation,[],[f24])).
% 3.97/0.97  
% 3.97/0.97  fof(f1,axiom,(
% 3.97/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f12,plain,(
% 3.97/0.97    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.97/0.97    inference(ennf_transformation,[],[f1])).
% 3.97/0.97  
% 3.97/0.97  fof(f25,plain,(
% 3.97/0.97    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f12])).
% 3.97/0.97  
% 3.97/0.97  fof(f8,axiom,(
% 3.97/0.97    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f22,plain,(
% 3.97/0.97    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.97/0.97    inference(nnf_transformation,[],[f8])).
% 3.97/0.97  
% 3.97/0.97  fof(f39,plain,(
% 3.97/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f22])).
% 3.97/0.97  
% 3.97/0.97  fof(f41,plain,(
% 3.97/0.97    r2_hidden(sK4,sK3)),
% 3.97/0.97    inference(cnf_transformation,[],[f24])).
% 3.97/0.97  
% 3.97/0.97  fof(f2,axiom,(
% 3.97/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f11,plain,(
% 3.97/0.97    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.97/0.97    inference(rectify,[],[f2])).
% 3.97/0.97  
% 3.97/0.97  fof(f13,plain,(
% 3.97/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.97/0.97    inference(ennf_transformation,[],[f11])).
% 3.97/0.97  
% 3.97/0.97  fof(f19,plain,(
% 3.97/0.97    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.97/0.97    introduced(choice_axiom,[])).
% 3.97/0.97  
% 3.97/0.97  fof(f20,plain,(
% 3.97/0.97    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.97/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f19])).
% 3.97/0.97  
% 3.97/0.97  fof(f28,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f20])).
% 3.97/0.97  
% 3.97/0.97  fof(f6,axiom,(
% 3.97/0.97    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f35,plain,(
% 3.97/0.97    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f6])).
% 3.97/0.97  
% 3.97/0.97  fof(f7,axiom,(
% 3.97/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f21,plain,(
% 3.97/0.97    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.97/0.97    inference(nnf_transformation,[],[f7])).
% 3.97/0.97  
% 3.97/0.97  fof(f36,plain,(
% 3.97/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f21])).
% 3.97/0.97  
% 3.97/0.97  fof(f3,axiom,(
% 3.97/0.97    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f14,plain,(
% 3.97/0.97    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.97/0.97    inference(ennf_transformation,[],[f3])).
% 3.97/0.97  
% 3.97/0.97  fof(f30,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f14])).
% 3.97/0.97  
% 3.97/0.97  fof(f5,axiom,(
% 3.97/0.97    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f16,plain,(
% 3.97/0.97    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 3.97/0.97    inference(ennf_transformation,[],[f5])).
% 3.97/0.97  
% 3.97/0.97  fof(f34,plain,(
% 3.97/0.97    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.97/0.97    inference(cnf_transformation,[],[f16])).
% 3.97/0.97  
% 3.97/0.97  fof(f4,axiom,(
% 3.97/0.97    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.97/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.97/0.97  
% 3.97/0.97  fof(f15,plain,(
% 3.97/0.97    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.97/0.97    inference(ennf_transformation,[],[f4])).
% 3.97/0.97  
% 3.97/0.97  fof(f31,plain,(
% 3.97/0.97    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.97/0.97    inference(cnf_transformation,[],[f15])).
% 3.97/0.97  
% 3.97/0.97  fof(f43,plain,(
% 3.97/0.97    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 3.97/0.97    inference(cnf_transformation,[],[f24])).
% 3.97/0.97  
% 3.97/0.97  cnf(c_18,negated_conjecture,
% 3.97/0.97      ( r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
% 3.97/0.97      inference(cnf_transformation,[],[f40]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_710,plain,
% 3.97/0.97      ( r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_16,negated_conjecture,
% 3.97/0.97      ( r1_xboole_0(sK3,sK2) ),
% 3.97/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_712,plain,
% 3.97/0.97      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_0,plain,
% 3.97/0.97      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.97/0.97      inference(cnf_transformation,[],[f25]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_728,plain,
% 3.97/0.97      ( r1_xboole_0(X0,X1) != iProver_top
% 3.97/0.97      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1193,plain,
% 3.97/0.97      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_712,c_728]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_13,plain,
% 3.97/0.97      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
% 3.97/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_715,plain,
% 3.97/0.97      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
% 3.97/0.97      | r2_hidden(X1,X0) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_17,negated_conjecture,
% 3.97/0.97      ( r2_hidden(sK4,sK3) ),
% 3.97/0.97      inference(cnf_transformation,[],[f41]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_711,plain,
% 3.97/0.97      ( r2_hidden(sK4,sK3) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1,plain,
% 3.97/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.97/0.97      inference(cnf_transformation,[],[f28]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_727,plain,
% 3.97/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.97/0.97      | r2_hidden(X0,X2) != iProver_top
% 3.97/0.97      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_2838,plain,
% 3.97/0.97      ( r2_hidden(sK4,X0) != iProver_top
% 3.97/0.97      | r1_xboole_0(X0,sK3) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_711,c_727]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3183,plain,
% 3.97/0.97      ( k4_xboole_0(X0,k1_tarski(sK4)) = X0
% 3.97/0.97      | r1_xboole_0(X0,sK3) != iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_715,c_2838]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3335,plain,
% 3.97/0.97      ( k4_xboole_0(sK2,k1_tarski(sK4)) = sK2 ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1193,c_3183]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_10,plain,
% 3.97/0.97      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 3.97/0.97      inference(cnf_transformation,[],[f35]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_718,plain,
% 3.97/0.97      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1192,plain,
% 3.97/0.97      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_718,c_728]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_12,plain,
% 3.97/0.97      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.97/0.97      inference(cnf_transformation,[],[f36]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_716,plain,
% 3.97/0.97      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1374,plain,
% 3.97/0.97      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_1192,c_716]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3465,plain,
% 3.97/0.97      ( k4_xboole_0(k1_tarski(sK4),sK2) = k1_tarski(sK4) ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_3335,c_1374]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_4,plain,
% 3.97/0.97      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 3.97/0.97      inference(cnf_transformation,[],[f30]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_724,plain,
% 3.97/0.97      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 3.97/0.97      | r1_xboole_0(X0,X2) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_3602,plain,
% 3.97/0.97      ( r1_tarski(X0,k1_tarski(sK4)) != iProver_top
% 3.97/0.97      | r1_xboole_0(X0,sK2) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_3465,c_724]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_16927,plain,
% 3.97/0.97      ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK2) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_710,c_3602]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_9,plain,
% 3.97/0.97      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 3.97/0.97      inference(cnf_transformation,[],[f34]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_719,plain,
% 3.97/0.97      ( r1_xboole_0(X0,X1) = iProver_top
% 3.97/0.97      | r1_xboole_0(k3_xboole_0(X0,X1),X1) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_16934,plain,
% 3.97/0.97      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_16927,c_719]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_17216,plain,
% 3.97/0.97      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 3.97/0.97      inference(superposition,[status(thm)],[c_16934,c_728]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1163,plain,
% 3.97/0.97      ( r1_xboole_0(sK2,sK3) | ~ r1_xboole_0(sK3,sK2) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_1164,plain,
% 3.97/0.97      ( r1_xboole_0(sK2,sK3) = iProver_top
% 3.97/0.97      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_1163]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_8,plain,
% 3.97/0.97      ( ~ r1_xboole_0(X0,X1)
% 3.97/0.97      | ~ r1_xboole_0(X0,X2)
% 3.97/0.97      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.97/0.97      inference(cnf_transformation,[],[f31]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_927,plain,
% 3.97/0.97      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
% 3.97/0.97      | ~ r1_xboole_0(sK2,sK3)
% 3.97/0.97      | ~ r1_xboole_0(sK2,sK1) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_928,plain,
% 3.97/0.97      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
% 3.97/0.97      | r1_xboole_0(sK2,sK3) != iProver_top
% 3.97/0.97      | r1_xboole_0(sK2,sK1) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_840,plain,
% 3.97/0.97      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
% 3.97/0.97      | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
% 3.97/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_841,plain,
% 3.97/0.97      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) = iProver_top
% 3.97/0.97      | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_840]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_15,negated_conjecture,
% 3.97/0.97      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
% 3.97/0.97      inference(cnf_transformation,[],[f43]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_22,plain,
% 3.97/0.97      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) != iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(c_21,plain,
% 3.97/0.97      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 3.97/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.97/0.97  
% 3.97/0.97  cnf(contradiction,plain,
% 3.97/0.97      ( $false ),
% 3.97/0.97      inference(minisat,
% 3.97/0.97                [status(thm)],
% 3.97/0.97                [c_17216,c_1164,c_928,c_841,c_22,c_21]) ).
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.97/0.97  
% 3.97/0.97  ------                               Statistics
% 3.97/0.97  
% 3.97/0.97  ------ General
% 3.97/0.97  
% 3.97/0.97  abstr_ref_over_cycles:                  0
% 3.97/0.97  abstr_ref_under_cycles:                 0
% 3.97/0.97  gc_basic_clause_elim:                   0
% 3.97/0.97  forced_gc_time:                         0
% 3.97/0.97  parsing_time:                           0.01
% 3.97/0.97  unif_index_cands_time:                  0.
% 3.97/0.97  unif_index_add_time:                    0.
% 3.97/0.97  orderings_time:                         0.
% 3.97/0.97  out_proof_time:                         0.008
% 3.97/0.97  total_time:                             0.457
% 3.97/0.97  num_of_symbols:                         43
% 3.97/0.97  num_of_terms:                           17377
% 3.97/0.97  
% 3.97/0.97  ------ Preprocessing
% 3.97/0.97  
% 3.97/0.97  num_of_splits:                          0
% 3.97/0.97  num_of_split_atoms:                     0
% 3.97/0.97  num_of_reused_defs:                     0
% 3.97/0.97  num_eq_ax_congr_red:                    6
% 3.97/0.97  num_of_sem_filtered_clauses:            1
% 3.97/0.97  num_of_subtypes:                        0
% 3.97/0.97  monotx_restored_types:                  0
% 3.97/0.97  sat_num_of_epr_types:                   0
% 3.97/0.97  sat_num_of_non_cyclic_types:            0
% 3.97/0.97  sat_guarded_non_collapsed_types:        0
% 3.97/0.97  num_pure_diseq_elim:                    0
% 3.97/0.97  simp_replaced_by:                       0
% 3.97/0.97  res_preprocessed:                       76
% 3.97/0.97  prep_upred:                             0
% 3.97/0.97  prep_unflattend:                        0
% 3.97/0.97  smt_new_axioms:                         0
% 3.97/0.97  pred_elim_cands:                        3
% 3.97/0.97  pred_elim:                              0
% 3.97/0.97  pred_elim_cl:                           0
% 3.97/0.97  pred_elim_cycles:                       1
% 3.97/0.97  merged_defs:                            12
% 3.97/0.97  merged_defs_ncl:                        0
% 3.97/0.97  bin_hyper_res:                          12
% 3.97/0.97  prep_cycles:                            3
% 3.97/0.97  pred_elim_time:                         0.
% 3.97/0.97  splitting_time:                         0.
% 3.97/0.97  sem_filter_time:                        0.
% 3.97/0.97  monotx_time:                            0.001
% 3.97/0.97  subtype_inf_time:                       0.
% 3.97/0.97  
% 3.97/0.97  ------ Problem properties
% 3.97/0.97  
% 3.97/0.97  clauses:                                19
% 3.97/0.97  conjectures:                            4
% 3.97/0.97  epr:                                    4
% 3.97/0.97  horn:                                   16
% 3.97/0.97  ground:                                 4
% 3.97/0.97  unary:                                  5
% 3.97/0.97  binary:                                 12
% 3.97/0.97  lits:                                   35
% 3.97/0.97  lits_eq:                                4
% 3.97/0.97  fd_pure:                                0
% 3.97/0.97  fd_pseudo:                              0
% 3.97/0.97  fd_cond:                                0
% 3.97/0.97  fd_pseudo_cond:                         0
% 3.97/0.97  ac_symbols:                             0
% 3.97/0.97  
% 3.97/0.97  ------ Propositional Solver
% 3.97/0.97  
% 3.97/0.97  prop_solver_calls:                      24
% 3.97/0.97  prop_fast_solver_calls:                 526
% 3.97/0.97  smt_solver_calls:                       0
% 3.97/0.97  smt_fast_solver_calls:                  0
% 3.97/0.97  prop_num_of_clauses:                    7302
% 3.97/0.97  prop_preprocess_simplified:             13252
% 3.97/0.97  prop_fo_subsumed:                       1
% 3.97/0.97  prop_solver_time:                       0.
% 3.97/0.97  smt_solver_time:                        0.
% 3.97/0.97  smt_fast_solver_time:                   0.
% 3.97/0.97  prop_fast_solver_time:                  0.
% 3.97/0.97  prop_unsat_core_time:                   0.001
% 3.97/0.97  
% 3.97/0.97  ------ QBF
% 3.97/0.97  
% 3.97/0.97  qbf_q_res:                              0
% 3.97/0.97  qbf_num_tautologies:                    0
% 3.97/0.97  qbf_prep_cycles:                        0
% 3.97/0.97  
% 3.97/0.97  ------ BMC1
% 3.97/0.97  
% 3.97/0.97  bmc1_current_bound:                     -1
% 3.97/0.97  bmc1_last_solved_bound:                 -1
% 3.97/0.97  bmc1_unsat_core_size:                   -1
% 3.97/0.97  bmc1_unsat_core_parents_size:           -1
% 3.97/0.97  bmc1_merge_next_fun:                    0
% 3.97/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.97/0.97  
% 3.97/0.97  ------ Instantiation
% 3.97/0.97  
% 3.97/0.97  inst_num_of_clauses:                    1879
% 3.97/0.97  inst_num_in_passive:                    409
% 3.97/0.97  inst_num_in_active:                     677
% 3.97/0.97  inst_num_in_unprocessed:                795
% 3.97/0.97  inst_num_of_loops:                      790
% 3.97/0.97  inst_num_of_learning_restarts:          0
% 3.97/0.97  inst_num_moves_active_passive:          112
% 3.97/0.97  inst_lit_activity:                      0
% 3.97/0.97  inst_lit_activity_moves:                0
% 3.97/0.97  inst_num_tautologies:                   0
% 3.97/0.97  inst_num_prop_implied:                  0
% 3.97/0.97  inst_num_existing_simplified:           0
% 3.97/0.97  inst_num_eq_res_simplified:             0
% 3.97/0.97  inst_num_child_elim:                    0
% 3.97/0.97  inst_num_of_dismatching_blockings:      1302
% 3.97/0.97  inst_num_of_non_proper_insts:           1775
% 3.97/0.97  inst_num_of_duplicates:                 0
% 3.97/0.97  inst_inst_num_from_inst_to_res:         0
% 3.97/0.97  inst_dismatching_checking_time:         0.
% 3.97/0.97  
% 3.97/0.97  ------ Resolution
% 3.97/0.97  
% 3.97/0.97  res_num_of_clauses:                     0
% 3.97/0.97  res_num_in_passive:                     0
% 3.97/0.97  res_num_in_active:                      0
% 3.97/0.97  res_num_of_loops:                       79
% 3.97/0.97  res_forward_subset_subsumed:            101
% 3.97/0.97  res_backward_subset_subsumed:           4
% 3.97/0.97  res_forward_subsumed:                   0
% 3.97/0.97  res_backward_subsumed:                  0
% 3.97/0.97  res_forward_subsumption_resolution:     0
% 3.97/0.97  res_backward_subsumption_resolution:    0
% 3.97/0.97  res_clause_to_clause_subsumption:       4708
% 3.97/0.97  res_orphan_elimination:                 0
% 3.97/0.97  res_tautology_del:                      124
% 3.97/0.97  res_num_eq_res_simplified:              0
% 3.97/0.97  res_num_sel_changes:                    0
% 3.97/0.97  res_moves_from_active_to_pass:          0
% 3.97/0.97  
% 3.97/0.97  ------ Superposition
% 3.97/0.97  
% 3.97/0.97  sup_time_total:                         0.
% 3.97/0.97  sup_time_generating:                    0.
% 3.97/0.97  sup_time_sim_full:                      0.
% 3.97/0.97  sup_time_sim_immed:                     0.
% 3.97/0.97  
% 3.97/0.97  sup_num_of_clauses:                     661
% 3.97/0.97  sup_num_in_active:                      157
% 3.97/0.97  sup_num_in_passive:                     504
% 3.97/0.97  sup_num_of_loops:                       156
% 3.97/0.97  sup_fw_superposition:                   454
% 3.97/0.97  sup_bw_superposition:                   981
% 3.97/0.97  sup_immediate_simplified:               204
% 3.97/0.97  sup_given_eliminated:                   0
% 3.97/0.97  comparisons_done:                       0
% 3.97/0.97  comparisons_avoided:                    0
% 3.97/0.97  
% 3.97/0.97  ------ Simplifications
% 3.97/0.97  
% 3.97/0.97  
% 3.97/0.97  sim_fw_subset_subsumed:                 4
% 3.97/0.97  sim_bw_subset_subsumed:                 0
% 3.97/0.97  sim_fw_subsumed:                        64
% 3.97/0.97  sim_bw_subsumed:                        1
% 3.97/0.97  sim_fw_subsumption_res:                 0
% 3.97/0.97  sim_bw_subsumption_res:                 0
% 3.97/0.97  sim_tautology_del:                      59
% 3.97/0.97  sim_eq_tautology_del:                   21
% 3.97/0.97  sim_eq_res_simp:                        0
% 3.97/0.97  sim_fw_demodulated:                     74
% 3.97/0.97  sim_bw_demodulated:                     0
% 3.97/0.97  sim_light_normalised:                   67
% 3.97/0.97  sim_joinable_taut:                      0
% 3.97/0.97  sim_joinable_simp:                      0
% 3.97/0.97  sim_ac_normalised:                      0
% 3.97/0.97  sim_smt_subsumption:                    0
% 3.97/0.97  
%------------------------------------------------------------------------------
