%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:32 EST 2020

% Result     : Theorem 11.86s
% Output     : CNFRefutation 11.86s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 278 expanded)
%              Number of clauses        :   54 ( 138 expanded)
%              Number of leaves         :    8 (  54 expanded)
%              Depth                    :   23
%              Number of atoms          :  160 ( 717 expanded)
%              Number of equality atoms :   62 ( 181 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK2,sK3))
      & r1_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK2,sK3))
    & r1_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f11,f14])).

fof(f26,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_112,plain,
    ( k4_xboole_0(k4_xboole_0(X0_36,X1_36),X2_36) = k4_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_113,plain,
    ( k2_xboole_0(X0_36,k4_xboole_0(X1_36,X0_36)) = k2_xboole_0(X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_8,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_108,plain,
    ( r1_xboole_0(k4_xboole_0(X0_36,X1_36),X1_36) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_293,plain,
    ( r1_xboole_0(k4_xboole_0(X0_36,X1_36),X1_36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_108])).

cnf(c_707,plain,
    ( r1_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)),X2_36) = iProver_top ),
    inference(superposition,[status(thm)],[c_112,c_293])).

cnf(c_717,plain,
    ( r1_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)),k4_xboole_0(X2_36,X1_36)) = iProver_top ),
    inference(superposition,[status(thm)],[c_113,c_707])).

cnf(c_800,plain,
    ( r1_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)),k4_xboole_0(k4_xboole_0(X2_36,X1_36),X1_36)) = iProver_top ),
    inference(superposition,[status(thm)],[c_113,c_717])).

cnf(c_802,plain,
    ( r1_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)),k4_xboole_0(X2_36,k2_xboole_0(X1_36,X1_36))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_800,c_112])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_115,plain,
    ( r2_hidden(sK0(X0_36,X1_36),X1_36)
    | r1_xboole_0(X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_288,plain,
    ( r2_hidden(sK0(X0_36,X1_36),X1_36) = iProver_top
    | r1_xboole_0(X0_36,X1_36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_116,plain,
    ( ~ r2_hidden(X0_37,X0_36)
    | ~ r2_hidden(X0_37,X1_36)
    | ~ r1_xboole_0(X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_287,plain,
    ( r2_hidden(X0_37,X0_36) != iProver_top
    | r2_hidden(X0_37,X1_36) != iProver_top
    | r1_xboole_0(X1_36,X0_36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_116])).

cnf(c_908,plain,
    ( r2_hidden(sK0(X0_36,X1_36),X2_36) != iProver_top
    | r1_xboole_0(X1_36,X2_36) != iProver_top
    | r1_xboole_0(X0_36,X1_36) = iProver_top ),
    inference(superposition,[status(thm)],[c_288,c_287])).

cnf(c_2419,plain,
    ( r1_xboole_0(X0_36,X0_36) != iProver_top
    | r1_xboole_0(X1_36,X0_36) = iProver_top ),
    inference(superposition,[status(thm)],[c_288,c_908])).

cnf(c_4522,plain,
    ( r1_xboole_0(X0_36,k4_xboole_0(X1_36,k2_xboole_0(X1_36,X1_36))) = iProver_top ),
    inference(superposition,[status(thm)],[c_802,c_2419])).

cnf(c_708,plain,
    ( k2_xboole_0(X0_36,k4_xboole_0(X1_36,k2_xboole_0(X2_36,X0_36))) = k2_xboole_0(X0_36,k4_xboole_0(X1_36,X2_36)) ),
    inference(superposition,[status(thm)],[c_112,c_113])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_109,plain,
    ( ~ r1_xboole_0(X0_36,X1_36)
    | ~ r1_xboole_0(X0_36,X2_36)
    | r1_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_292,plain,
    ( r1_xboole_0(X0_36,X1_36) != iProver_top
    | r1_xboole_0(X0_36,X2_36) != iProver_top
    | r1_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_109])).

cnf(c_1584,plain,
    ( r1_xboole_0(X0_36,X1_36) != iProver_top
    | r1_xboole_0(X0_36,k4_xboole_0(X2_36,k2_xboole_0(X3_36,X1_36))) != iProver_top
    | r1_xboole_0(X0_36,k2_xboole_0(X1_36,k4_xboole_0(X2_36,X3_36))) = iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_292])).

cnf(c_18655,plain,
    ( r1_xboole_0(X0_36,X1_36) != iProver_top
    | r1_xboole_0(X0_36,k2_xboole_0(X1_36,k4_xboole_0(X1_36,X1_36))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_1584])).

cnf(c_18725,plain,
    ( r1_xboole_0(X0_36,X1_36) != iProver_top
    | r1_xboole_0(X0_36,k2_xboole_0(X1_36,X1_36)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18655,c_113])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_114,plain,
    ( r2_hidden(sK0(X0_36,X1_36),X0_36)
    | r1_xboole_0(X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_289,plain,
    ( r2_hidden(sK0(X0_36,X1_36),X0_36) = iProver_top
    | r1_xboole_0(X0_36,X1_36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_114])).

cnf(c_998,plain,
    ( r2_hidden(sK0(X0_36,X1_36),X2_36) != iProver_top
    | r1_xboole_0(X0_36,X2_36) != iProver_top
    | r1_xboole_0(X0_36,X1_36) = iProver_top ),
    inference(superposition,[status(thm)],[c_289,c_287])).

cnf(c_4006,plain,
    ( r1_xboole_0(X0_36,X0_36) != iProver_top
    | r1_xboole_0(X0_36,X1_36) = iProver_top ),
    inference(superposition,[status(thm)],[c_289,c_998])).

cnf(c_19134,plain,
    ( r1_xboole_0(k2_xboole_0(X0_36,X0_36),X0_36) != iProver_top
    | r1_xboole_0(k2_xboole_0(X0_36,X0_36),X1_36) = iProver_top ),
    inference(superposition,[status(thm)],[c_18725,c_4006])).

cnf(c_20564,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X0_36,X0_36)),k4_xboole_0(X0_36,k2_xboole_0(X0_36,X0_36))),X1_36) = iProver_top ),
    inference(superposition,[status(thm)],[c_4522,c_19134])).

cnf(c_1001,plain,
    ( k2_xboole_0(k4_xboole_0(X0_36,X1_36),k4_xboole_0(X2_36,k2_xboole_0(X1_36,X0_36))) = k2_xboole_0(k4_xboole_0(X0_36,X1_36),k4_xboole_0(X2_36,X1_36)) ),
    inference(superposition,[status(thm)],[c_113,c_708])).

cnf(c_2544,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0_36,X1_36),X1_36),k4_xboole_0(X2_36,k2_xboole_0(X1_36,X0_36))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0_36,X1_36),X1_36),k4_xboole_0(X2_36,X1_36)) ),
    inference(superposition,[status(thm)],[c_113,c_1001])).

cnf(c_2605,plain,
    ( k2_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X1_36)),k4_xboole_0(X2_36,k2_xboole_0(X1_36,X0_36))) = k2_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X1_36)),k4_xboole_0(X2_36,X1_36)) ),
    inference(demodulation,[status(thm)],[c_2544,c_112])).

cnf(c_20579,plain,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X0_36,X0_36)),k4_xboole_0(X0_36,X0_36)),X1_36) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20564,c_2605])).

cnf(c_20626,plain,
    ( r1_xboole_0(X0_36,k2_xboole_0(k4_xboole_0(X1_36,k2_xboole_0(X1_36,X1_36)),k4_xboole_0(X1_36,X1_36))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20579,c_2419])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_111,plain,
    ( r1_xboole_0(X0_36,X1_36)
    | ~ r1_xboole_0(X0_36,k2_xboole_0(X2_36,X1_36)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_290,plain,
    ( r1_xboole_0(X0_36,X1_36) = iProver_top
    | r1_xboole_0(X0_36,k2_xboole_0(X2_36,X1_36)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_111])).

cnf(c_20950,plain,
    ( r1_xboole_0(X0_36,k4_xboole_0(X1_36,X1_36)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20626,c_290])).

cnf(c_20989,plain,
    ( r1_xboole_0(X0_36,k4_xboole_0(X1_36,k2_xboole_0(X2_36,k4_xboole_0(X1_36,X2_36)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_112,c_20950])).

cnf(c_20999,plain,
    ( r1_xboole_0(X0_36,k4_xboole_0(X1_36,k2_xboole_0(X2_36,X1_36))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20989,c_113])).

cnf(c_22103,plain,
    ( r1_xboole_0(X0_36,X1_36) != iProver_top
    | r1_xboole_0(X0_36,k2_xboole_0(X1_36,k4_xboole_0(X1_36,X2_36))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20999,c_1584])).

cnf(c_42781,plain,
    ( r1_xboole_0(X0_36,X1_36) != iProver_top
    | r1_xboole_0(X0_36,k4_xboole_0(X1_36,X2_36)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22103,c_290])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_107,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_294,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_107])).

cnf(c_42818,plain,
    ( r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_42781,c_294])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_11,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42818,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.86/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.86/2.00  
% 11.86/2.00  ------  iProver source info
% 11.86/2.00  
% 11.86/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.86/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.86/2.00  git: non_committed_changes: false
% 11.86/2.00  git: last_make_outside_of_git: false
% 11.86/2.00  
% 11.86/2.00  ------ 
% 11.86/2.00  
% 11.86/2.00  ------ Input Options
% 11.86/2.00  
% 11.86/2.00  --out_options                           all
% 11.86/2.00  --tptp_safe_out                         true
% 11.86/2.00  --problem_path                          ""
% 11.86/2.00  --include_path                          ""
% 11.86/2.00  --clausifier                            res/vclausify_rel
% 11.86/2.00  --clausifier_options                    ""
% 11.86/2.00  --stdin                                 false
% 11.86/2.00  --stats_out                             all
% 11.86/2.00  
% 11.86/2.00  ------ General Options
% 11.86/2.00  
% 11.86/2.00  --fof                                   false
% 11.86/2.00  --time_out_real                         305.
% 11.86/2.00  --time_out_virtual                      -1.
% 11.86/2.00  --symbol_type_check                     false
% 11.86/2.00  --clausify_out                          false
% 11.86/2.00  --sig_cnt_out                           false
% 11.86/2.00  --trig_cnt_out                          false
% 11.86/2.00  --trig_cnt_out_tolerance                1.
% 11.86/2.00  --trig_cnt_out_sk_spl                   false
% 11.86/2.00  --abstr_cl_out                          false
% 11.86/2.00  
% 11.86/2.00  ------ Global Options
% 11.86/2.00  
% 11.86/2.00  --schedule                              default
% 11.86/2.00  --add_important_lit                     false
% 11.86/2.00  --prop_solver_per_cl                    1000
% 11.86/2.00  --min_unsat_core                        false
% 11.86/2.00  --soft_assumptions                      false
% 11.86/2.00  --soft_lemma_size                       3
% 11.86/2.00  --prop_impl_unit_size                   0
% 11.86/2.00  --prop_impl_unit                        []
% 11.86/2.00  --share_sel_clauses                     true
% 11.86/2.00  --reset_solvers                         false
% 11.86/2.00  --bc_imp_inh                            [conj_cone]
% 11.86/2.00  --conj_cone_tolerance                   3.
% 11.86/2.00  --extra_neg_conj                        none
% 11.86/2.00  --large_theory_mode                     true
% 11.86/2.00  --prolific_symb_bound                   200
% 11.86/2.00  --lt_threshold                          2000
% 11.86/2.00  --clause_weak_htbl                      true
% 11.86/2.00  --gc_record_bc_elim                     false
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing Options
% 11.86/2.00  
% 11.86/2.00  --preprocessing_flag                    true
% 11.86/2.00  --time_out_prep_mult                    0.1
% 11.86/2.00  --splitting_mode                        input
% 11.86/2.00  --splitting_grd                         true
% 11.86/2.00  --splitting_cvd                         false
% 11.86/2.00  --splitting_cvd_svl                     false
% 11.86/2.00  --splitting_nvd                         32
% 11.86/2.00  --sub_typing                            true
% 11.86/2.00  --prep_gs_sim                           true
% 11.86/2.00  --prep_unflatten                        true
% 11.86/2.00  --prep_res_sim                          true
% 11.86/2.00  --prep_upred                            true
% 11.86/2.00  --prep_sem_filter                       exhaustive
% 11.86/2.00  --prep_sem_filter_out                   false
% 11.86/2.00  --pred_elim                             true
% 11.86/2.00  --res_sim_input                         true
% 11.86/2.00  --eq_ax_congr_red                       true
% 11.86/2.00  --pure_diseq_elim                       true
% 11.86/2.00  --brand_transform                       false
% 11.86/2.00  --non_eq_to_eq                          false
% 11.86/2.00  --prep_def_merge                        true
% 11.86/2.00  --prep_def_merge_prop_impl              false
% 11.86/2.00  --prep_def_merge_mbd                    true
% 11.86/2.00  --prep_def_merge_tr_red                 false
% 11.86/2.00  --prep_def_merge_tr_cl                  false
% 11.86/2.00  --smt_preprocessing                     true
% 11.86/2.00  --smt_ac_axioms                         fast
% 11.86/2.00  --preprocessed_out                      false
% 11.86/2.00  --preprocessed_stats                    false
% 11.86/2.00  
% 11.86/2.00  ------ Abstraction refinement Options
% 11.86/2.00  
% 11.86/2.00  --abstr_ref                             []
% 11.86/2.00  --abstr_ref_prep                        false
% 11.86/2.00  --abstr_ref_until_sat                   false
% 11.86/2.00  --abstr_ref_sig_restrict                funpre
% 11.86/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.86/2.00  --abstr_ref_under                       []
% 11.86/2.00  
% 11.86/2.00  ------ SAT Options
% 11.86/2.00  
% 11.86/2.00  --sat_mode                              false
% 11.86/2.00  --sat_fm_restart_options                ""
% 11.86/2.00  --sat_gr_def                            false
% 11.86/2.00  --sat_epr_types                         true
% 11.86/2.00  --sat_non_cyclic_types                  false
% 11.86/2.00  --sat_finite_models                     false
% 11.86/2.00  --sat_fm_lemmas                         false
% 11.86/2.00  --sat_fm_prep                           false
% 11.86/2.00  --sat_fm_uc_incr                        true
% 11.86/2.00  --sat_out_model                         small
% 11.86/2.00  --sat_out_clauses                       false
% 11.86/2.00  
% 11.86/2.00  ------ QBF Options
% 11.86/2.00  
% 11.86/2.00  --qbf_mode                              false
% 11.86/2.00  --qbf_elim_univ                         false
% 11.86/2.00  --qbf_dom_inst                          none
% 11.86/2.00  --qbf_dom_pre_inst                      false
% 11.86/2.00  --qbf_sk_in                             false
% 11.86/2.00  --qbf_pred_elim                         true
% 11.86/2.00  --qbf_split                             512
% 11.86/2.00  
% 11.86/2.00  ------ BMC1 Options
% 11.86/2.00  
% 11.86/2.00  --bmc1_incremental                      false
% 11.86/2.00  --bmc1_axioms                           reachable_all
% 11.86/2.00  --bmc1_min_bound                        0
% 11.86/2.00  --bmc1_max_bound                        -1
% 11.86/2.00  --bmc1_max_bound_default                -1
% 11.86/2.00  --bmc1_symbol_reachability              true
% 11.86/2.00  --bmc1_property_lemmas                  false
% 11.86/2.00  --bmc1_k_induction                      false
% 11.86/2.00  --bmc1_non_equiv_states                 false
% 11.86/2.00  --bmc1_deadlock                         false
% 11.86/2.00  --bmc1_ucm                              false
% 11.86/2.00  --bmc1_add_unsat_core                   none
% 11.86/2.00  --bmc1_unsat_core_children              false
% 11.86/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.86/2.00  --bmc1_out_stat                         full
% 11.86/2.00  --bmc1_ground_init                      false
% 11.86/2.00  --bmc1_pre_inst_next_state              false
% 11.86/2.00  --bmc1_pre_inst_state                   false
% 11.86/2.00  --bmc1_pre_inst_reach_state             false
% 11.86/2.00  --bmc1_out_unsat_core                   false
% 11.86/2.00  --bmc1_aig_witness_out                  false
% 11.86/2.00  --bmc1_verbose                          false
% 11.86/2.00  --bmc1_dump_clauses_tptp                false
% 11.86/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.86/2.00  --bmc1_dump_file                        -
% 11.86/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.86/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.86/2.00  --bmc1_ucm_extend_mode                  1
% 11.86/2.00  --bmc1_ucm_init_mode                    2
% 11.86/2.00  --bmc1_ucm_cone_mode                    none
% 11.86/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.86/2.00  --bmc1_ucm_relax_model                  4
% 11.86/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.86/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.86/2.00  --bmc1_ucm_layered_model                none
% 11.86/2.00  --bmc1_ucm_max_lemma_size               10
% 11.86/2.00  
% 11.86/2.00  ------ AIG Options
% 11.86/2.00  
% 11.86/2.00  --aig_mode                              false
% 11.86/2.00  
% 11.86/2.00  ------ Instantiation Options
% 11.86/2.00  
% 11.86/2.00  --instantiation_flag                    true
% 11.86/2.00  --inst_sos_flag                         true
% 11.86/2.00  --inst_sos_phase                        true
% 11.86/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel_side                     num_symb
% 11.86/2.00  --inst_solver_per_active                1400
% 11.86/2.00  --inst_solver_calls_frac                1.
% 11.86/2.00  --inst_passive_queue_type               priority_queues
% 11.86/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.86/2.00  --inst_passive_queues_freq              [25;2]
% 11.86/2.00  --inst_dismatching                      true
% 11.86/2.00  --inst_eager_unprocessed_to_passive     true
% 11.86/2.00  --inst_prop_sim_given                   true
% 11.86/2.00  --inst_prop_sim_new                     false
% 11.86/2.00  --inst_subs_new                         false
% 11.86/2.00  --inst_eq_res_simp                      false
% 11.86/2.00  --inst_subs_given                       false
% 11.86/2.00  --inst_orphan_elimination               true
% 11.86/2.00  --inst_learning_loop_flag               true
% 11.86/2.00  --inst_learning_start                   3000
% 11.86/2.00  --inst_learning_factor                  2
% 11.86/2.00  --inst_start_prop_sim_after_learn       3
% 11.86/2.00  --inst_sel_renew                        solver
% 11.86/2.00  --inst_lit_activity_flag                true
% 11.86/2.00  --inst_restr_to_given                   false
% 11.86/2.00  --inst_activity_threshold               500
% 11.86/2.00  --inst_out_proof                        true
% 11.86/2.00  
% 11.86/2.00  ------ Resolution Options
% 11.86/2.00  
% 11.86/2.00  --resolution_flag                       true
% 11.86/2.00  --res_lit_sel                           adaptive
% 11.86/2.00  --res_lit_sel_side                      none
% 11.86/2.00  --res_ordering                          kbo
% 11.86/2.00  --res_to_prop_solver                    active
% 11.86/2.00  --res_prop_simpl_new                    false
% 11.86/2.00  --res_prop_simpl_given                  true
% 11.86/2.00  --res_passive_queue_type                priority_queues
% 11.86/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.86/2.00  --res_passive_queues_freq               [15;5]
% 11.86/2.00  --res_forward_subs                      full
% 11.86/2.00  --res_backward_subs                     full
% 11.86/2.00  --res_forward_subs_resolution           true
% 11.86/2.00  --res_backward_subs_resolution          true
% 11.86/2.00  --res_orphan_elimination                true
% 11.86/2.00  --res_time_limit                        2.
% 11.86/2.00  --res_out_proof                         true
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Options
% 11.86/2.00  
% 11.86/2.00  --superposition_flag                    true
% 11.86/2.00  --sup_passive_queue_type                priority_queues
% 11.86/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.86/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.86/2.00  --demod_completeness_check              fast
% 11.86/2.00  --demod_use_ground                      true
% 11.86/2.00  --sup_to_prop_solver                    passive
% 11.86/2.00  --sup_prop_simpl_new                    true
% 11.86/2.00  --sup_prop_simpl_given                  true
% 11.86/2.00  --sup_fun_splitting                     true
% 11.86/2.00  --sup_smt_interval                      50000
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Simplification Setup
% 11.86/2.00  
% 11.86/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.86/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.86/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_immed_triv                        [TrivRules]
% 11.86/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_bw_main                     []
% 11.86/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.86/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_input_bw                          []
% 11.86/2.00  
% 11.86/2.00  ------ Combination Options
% 11.86/2.00  
% 11.86/2.00  --comb_res_mult                         3
% 11.86/2.00  --comb_sup_mult                         2
% 11.86/2.00  --comb_inst_mult                        10
% 11.86/2.00  
% 11.86/2.00  ------ Debug Options
% 11.86/2.00  
% 11.86/2.00  --dbg_backtrace                         false
% 11.86/2.00  --dbg_dump_prop_clauses                 false
% 11.86/2.00  --dbg_dump_prop_clauses_file            -
% 11.86/2.00  --dbg_out_stat                          false
% 11.86/2.00  ------ Parsing...
% 11.86/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.86/2.00  ------ Proving...
% 11.86/2.00  ------ Problem Properties 
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  clauses                                 11
% 11.86/2.00  conjectures                             2
% 11.86/2.00  EPR                                     2
% 11.86/2.00  Horn                                    9
% 11.86/2.00  unary                                   5
% 11.86/2.00  binary                                  4
% 11.86/2.00  lits                                    19
% 11.86/2.00  lits eq                                 2
% 11.86/2.00  fd_pure                                 0
% 11.86/2.00  fd_pseudo                               0
% 11.86/2.00  fd_cond                                 0
% 11.86/2.00  fd_pseudo_cond                          0
% 11.86/2.00  AC symbols                              0
% 11.86/2.00  
% 11.86/2.00  ------ Schedule dynamic 5 is on 
% 11.86/2.00  
% 11.86/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ 
% 11.86/2.00  Current options:
% 11.86/2.00  ------ 
% 11.86/2.00  
% 11.86/2.00  ------ Input Options
% 11.86/2.00  
% 11.86/2.00  --out_options                           all
% 11.86/2.00  --tptp_safe_out                         true
% 11.86/2.00  --problem_path                          ""
% 11.86/2.00  --include_path                          ""
% 11.86/2.00  --clausifier                            res/vclausify_rel
% 11.86/2.00  --clausifier_options                    ""
% 11.86/2.00  --stdin                                 false
% 11.86/2.00  --stats_out                             all
% 11.86/2.00  
% 11.86/2.00  ------ General Options
% 11.86/2.00  
% 11.86/2.00  --fof                                   false
% 11.86/2.00  --time_out_real                         305.
% 11.86/2.00  --time_out_virtual                      -1.
% 11.86/2.00  --symbol_type_check                     false
% 11.86/2.00  --clausify_out                          false
% 11.86/2.00  --sig_cnt_out                           false
% 11.86/2.00  --trig_cnt_out                          false
% 11.86/2.00  --trig_cnt_out_tolerance                1.
% 11.86/2.00  --trig_cnt_out_sk_spl                   false
% 11.86/2.00  --abstr_cl_out                          false
% 11.86/2.00  
% 11.86/2.00  ------ Global Options
% 11.86/2.00  
% 11.86/2.00  --schedule                              default
% 11.86/2.00  --add_important_lit                     false
% 11.86/2.00  --prop_solver_per_cl                    1000
% 11.86/2.00  --min_unsat_core                        false
% 11.86/2.00  --soft_assumptions                      false
% 11.86/2.00  --soft_lemma_size                       3
% 11.86/2.00  --prop_impl_unit_size                   0
% 11.86/2.00  --prop_impl_unit                        []
% 11.86/2.00  --share_sel_clauses                     true
% 11.86/2.00  --reset_solvers                         false
% 11.86/2.00  --bc_imp_inh                            [conj_cone]
% 11.86/2.00  --conj_cone_tolerance                   3.
% 11.86/2.00  --extra_neg_conj                        none
% 11.86/2.00  --large_theory_mode                     true
% 11.86/2.00  --prolific_symb_bound                   200
% 11.86/2.00  --lt_threshold                          2000
% 11.86/2.00  --clause_weak_htbl                      true
% 11.86/2.00  --gc_record_bc_elim                     false
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing Options
% 11.86/2.00  
% 11.86/2.00  --preprocessing_flag                    true
% 11.86/2.00  --time_out_prep_mult                    0.1
% 11.86/2.00  --splitting_mode                        input
% 11.86/2.00  --splitting_grd                         true
% 11.86/2.00  --splitting_cvd                         false
% 11.86/2.00  --splitting_cvd_svl                     false
% 11.86/2.00  --splitting_nvd                         32
% 11.86/2.00  --sub_typing                            true
% 11.86/2.00  --prep_gs_sim                           true
% 11.86/2.00  --prep_unflatten                        true
% 11.86/2.00  --prep_res_sim                          true
% 11.86/2.00  --prep_upred                            true
% 11.86/2.00  --prep_sem_filter                       exhaustive
% 11.86/2.00  --prep_sem_filter_out                   false
% 11.86/2.00  --pred_elim                             true
% 11.86/2.00  --res_sim_input                         true
% 11.86/2.00  --eq_ax_congr_red                       true
% 11.86/2.00  --pure_diseq_elim                       true
% 11.86/2.00  --brand_transform                       false
% 11.86/2.00  --non_eq_to_eq                          false
% 11.86/2.00  --prep_def_merge                        true
% 11.86/2.00  --prep_def_merge_prop_impl              false
% 11.86/2.00  --prep_def_merge_mbd                    true
% 11.86/2.00  --prep_def_merge_tr_red                 false
% 11.86/2.00  --prep_def_merge_tr_cl                  false
% 11.86/2.00  --smt_preprocessing                     true
% 11.86/2.00  --smt_ac_axioms                         fast
% 11.86/2.00  --preprocessed_out                      false
% 11.86/2.00  --preprocessed_stats                    false
% 11.86/2.00  
% 11.86/2.00  ------ Abstraction refinement Options
% 11.86/2.00  
% 11.86/2.00  --abstr_ref                             []
% 11.86/2.00  --abstr_ref_prep                        false
% 11.86/2.00  --abstr_ref_until_sat                   false
% 11.86/2.00  --abstr_ref_sig_restrict                funpre
% 11.86/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.86/2.00  --abstr_ref_under                       []
% 11.86/2.00  
% 11.86/2.00  ------ SAT Options
% 11.86/2.00  
% 11.86/2.00  --sat_mode                              false
% 11.86/2.00  --sat_fm_restart_options                ""
% 11.86/2.00  --sat_gr_def                            false
% 11.86/2.00  --sat_epr_types                         true
% 11.86/2.00  --sat_non_cyclic_types                  false
% 11.86/2.00  --sat_finite_models                     false
% 11.86/2.00  --sat_fm_lemmas                         false
% 11.86/2.00  --sat_fm_prep                           false
% 11.86/2.00  --sat_fm_uc_incr                        true
% 11.86/2.00  --sat_out_model                         small
% 11.86/2.00  --sat_out_clauses                       false
% 11.86/2.00  
% 11.86/2.00  ------ QBF Options
% 11.86/2.00  
% 11.86/2.00  --qbf_mode                              false
% 11.86/2.00  --qbf_elim_univ                         false
% 11.86/2.00  --qbf_dom_inst                          none
% 11.86/2.00  --qbf_dom_pre_inst                      false
% 11.86/2.00  --qbf_sk_in                             false
% 11.86/2.00  --qbf_pred_elim                         true
% 11.86/2.00  --qbf_split                             512
% 11.86/2.00  
% 11.86/2.00  ------ BMC1 Options
% 11.86/2.00  
% 11.86/2.00  --bmc1_incremental                      false
% 11.86/2.00  --bmc1_axioms                           reachable_all
% 11.86/2.00  --bmc1_min_bound                        0
% 11.86/2.00  --bmc1_max_bound                        -1
% 11.86/2.00  --bmc1_max_bound_default                -1
% 11.86/2.00  --bmc1_symbol_reachability              true
% 11.86/2.00  --bmc1_property_lemmas                  false
% 11.86/2.00  --bmc1_k_induction                      false
% 11.86/2.00  --bmc1_non_equiv_states                 false
% 11.86/2.00  --bmc1_deadlock                         false
% 11.86/2.00  --bmc1_ucm                              false
% 11.86/2.00  --bmc1_add_unsat_core                   none
% 11.86/2.00  --bmc1_unsat_core_children              false
% 11.86/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.86/2.00  --bmc1_out_stat                         full
% 11.86/2.00  --bmc1_ground_init                      false
% 11.86/2.00  --bmc1_pre_inst_next_state              false
% 11.86/2.00  --bmc1_pre_inst_state                   false
% 11.86/2.00  --bmc1_pre_inst_reach_state             false
% 11.86/2.00  --bmc1_out_unsat_core                   false
% 11.86/2.00  --bmc1_aig_witness_out                  false
% 11.86/2.00  --bmc1_verbose                          false
% 11.86/2.00  --bmc1_dump_clauses_tptp                false
% 11.86/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.86/2.00  --bmc1_dump_file                        -
% 11.86/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.86/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.86/2.00  --bmc1_ucm_extend_mode                  1
% 11.86/2.00  --bmc1_ucm_init_mode                    2
% 11.86/2.00  --bmc1_ucm_cone_mode                    none
% 11.86/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.86/2.00  --bmc1_ucm_relax_model                  4
% 11.86/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.86/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.86/2.00  --bmc1_ucm_layered_model                none
% 11.86/2.00  --bmc1_ucm_max_lemma_size               10
% 11.86/2.00  
% 11.86/2.00  ------ AIG Options
% 11.86/2.00  
% 11.86/2.00  --aig_mode                              false
% 11.86/2.00  
% 11.86/2.00  ------ Instantiation Options
% 11.86/2.00  
% 11.86/2.00  --instantiation_flag                    true
% 11.86/2.00  --inst_sos_flag                         true
% 11.86/2.00  --inst_sos_phase                        true
% 11.86/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.86/2.00  --inst_lit_sel_side                     none
% 11.86/2.00  --inst_solver_per_active                1400
% 11.86/2.00  --inst_solver_calls_frac                1.
% 11.86/2.00  --inst_passive_queue_type               priority_queues
% 11.86/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.86/2.00  --inst_passive_queues_freq              [25;2]
% 11.86/2.00  --inst_dismatching                      true
% 11.86/2.00  --inst_eager_unprocessed_to_passive     true
% 11.86/2.00  --inst_prop_sim_given                   true
% 11.86/2.00  --inst_prop_sim_new                     false
% 11.86/2.00  --inst_subs_new                         false
% 11.86/2.00  --inst_eq_res_simp                      false
% 11.86/2.00  --inst_subs_given                       false
% 11.86/2.00  --inst_orphan_elimination               true
% 11.86/2.00  --inst_learning_loop_flag               true
% 11.86/2.00  --inst_learning_start                   3000
% 11.86/2.00  --inst_learning_factor                  2
% 11.86/2.00  --inst_start_prop_sim_after_learn       3
% 11.86/2.00  --inst_sel_renew                        solver
% 11.86/2.00  --inst_lit_activity_flag                true
% 11.86/2.00  --inst_restr_to_given                   false
% 11.86/2.00  --inst_activity_threshold               500
% 11.86/2.00  --inst_out_proof                        true
% 11.86/2.00  
% 11.86/2.00  ------ Resolution Options
% 11.86/2.00  
% 11.86/2.00  --resolution_flag                       false
% 11.86/2.00  --res_lit_sel                           adaptive
% 11.86/2.00  --res_lit_sel_side                      none
% 11.86/2.00  --res_ordering                          kbo
% 11.86/2.00  --res_to_prop_solver                    active
% 11.86/2.00  --res_prop_simpl_new                    false
% 11.86/2.00  --res_prop_simpl_given                  true
% 11.86/2.00  --res_passive_queue_type                priority_queues
% 11.86/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.86/2.00  --res_passive_queues_freq               [15;5]
% 11.86/2.00  --res_forward_subs                      full
% 11.86/2.00  --res_backward_subs                     full
% 11.86/2.00  --res_forward_subs_resolution           true
% 11.86/2.00  --res_backward_subs_resolution          true
% 11.86/2.00  --res_orphan_elimination                true
% 11.86/2.00  --res_time_limit                        2.
% 11.86/2.00  --res_out_proof                         true
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Options
% 11.86/2.00  
% 11.86/2.00  --superposition_flag                    true
% 11.86/2.00  --sup_passive_queue_type                priority_queues
% 11.86/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.86/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.86/2.00  --demod_completeness_check              fast
% 11.86/2.00  --demod_use_ground                      true
% 11.86/2.00  --sup_to_prop_solver                    passive
% 11.86/2.00  --sup_prop_simpl_new                    true
% 11.86/2.00  --sup_prop_simpl_given                  true
% 11.86/2.00  --sup_fun_splitting                     true
% 11.86/2.00  --sup_smt_interval                      50000
% 11.86/2.00  
% 11.86/2.00  ------ Superposition Simplification Setup
% 11.86/2.00  
% 11.86/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.86/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.86/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.86/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.86/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_immed_triv                        [TrivRules]
% 11.86/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_immed_bw_main                     []
% 11.86/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.86/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.86/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.86/2.00  --sup_input_bw                          []
% 11.86/2.00  
% 11.86/2.00  ------ Combination Options
% 11.86/2.00  
% 11.86/2.00  --comb_res_mult                         3
% 11.86/2.00  --comb_sup_mult                         2
% 11.86/2.00  --comb_inst_mult                        10
% 11.86/2.00  
% 11.86/2.00  ------ Debug Options
% 11.86/2.00  
% 11.86/2.00  --dbg_backtrace                         false
% 11.86/2.00  --dbg_dump_prop_clauses                 false
% 11.86/2.00  --dbg_dump_prop_clauses_file            -
% 11.86/2.00  --dbg_out_stat                          false
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  ------ Proving...
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  % SZS status Theorem for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  fof(f3,axiom,(
% 11.86/2.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f20,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f3])).
% 11.86/2.00  
% 11.86/2.00  fof(f2,axiom,(
% 11.86/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f19,plain,(
% 11.86/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f2])).
% 11.86/2.00  
% 11.86/2.00  fof(f5,axiom,(
% 11.86/2.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f24,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f5])).
% 11.86/2.00  
% 11.86/2.00  fof(f1,axiom,(
% 11.86/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f8,plain,(
% 11.86/2.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.86/2.00    inference(rectify,[],[f1])).
% 11.86/2.00  
% 11.86/2.00  fof(f9,plain,(
% 11.86/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.86/2.00    inference(ennf_transformation,[],[f8])).
% 11.86/2.00  
% 11.86/2.00  fof(f12,plain,(
% 11.86/2.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f13,plain,(
% 11.86/2.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.86/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 11.86/2.00  
% 11.86/2.00  fof(f17,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f13])).
% 11.86/2.00  
% 11.86/2.00  fof(f18,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f13])).
% 11.86/2.00  
% 11.86/2.00  fof(f4,axiom,(
% 11.86/2.00    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f10,plain,(
% 11.86/2.00    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 11.86/2.00    inference(ennf_transformation,[],[f4])).
% 11.86/2.00  
% 11.86/2.00  fof(f21,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 11.86/2.00    inference(cnf_transformation,[],[f10])).
% 11.86/2.00  
% 11.86/2.00  fof(f16,plain,(
% 11.86/2.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f13])).
% 11.86/2.00  
% 11.86/2.00  fof(f23,plain,(
% 11.86/2.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 11.86/2.00    inference(cnf_transformation,[],[f10])).
% 11.86/2.00  
% 11.86/2.00  fof(f6,conjecture,(
% 11.86/2.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 11.86/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.86/2.00  
% 11.86/2.00  fof(f7,negated_conjecture,(
% 11.86/2.00    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 11.86/2.00    inference(negated_conjecture,[],[f6])).
% 11.86/2.00  
% 11.86/2.00  fof(f11,plain,(
% 11.86/2.00    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 11.86/2.00    inference(ennf_transformation,[],[f7])).
% 11.86/2.00  
% 11.86/2.00  fof(f14,plain,(
% 11.86/2.00    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) & r1_xboole_0(sK1,sK2))),
% 11.86/2.00    introduced(choice_axiom,[])).
% 11.86/2.00  
% 11.86/2.00  fof(f15,plain,(
% 11.86/2.00    ~r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) & r1_xboole_0(sK1,sK2)),
% 11.86/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f11,f14])).
% 11.86/2.00  
% 11.86/2.00  fof(f26,plain,(
% 11.86/2.00    ~r1_xboole_0(sK1,k4_xboole_0(sK2,sK3))),
% 11.86/2.00    inference(cnf_transformation,[],[f15])).
% 11.86/2.00  
% 11.86/2.00  fof(f25,plain,(
% 11.86/2.00    r1_xboole_0(sK1,sK2)),
% 11.86/2.00    inference(cnf_transformation,[],[f15])).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4,plain,
% 11.86/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f20]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_112,plain,
% 11.86/2.00      ( k4_xboole_0(k4_xboole_0(X0_36,X1_36),X2_36) = k4_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)) ),
% 11.86/2.00      inference(subtyping,[status(esa)],[c_4]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_3,plain,
% 11.86/2.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f19]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_113,plain,
% 11.86/2.00      ( k2_xboole_0(X0_36,k4_xboole_0(X1_36,X0_36)) = k2_xboole_0(X0_36,X1_36) ),
% 11.86/2.00      inference(subtyping,[status(esa)],[c_3]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_8,plain,
% 11.86/2.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f24]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_108,plain,
% 11.86/2.00      ( r1_xboole_0(k4_xboole_0(X0_36,X1_36),X1_36) ),
% 11.86/2.00      inference(subtyping,[status(esa)],[c_8]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_293,plain,
% 11.86/2.00      ( r1_xboole_0(k4_xboole_0(X0_36,X1_36),X1_36) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_108]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_707,plain,
% 11.86/2.00      ( r1_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)),X2_36) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_112,c_293]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_717,plain,
% 11.86/2.00      ( r1_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)),k4_xboole_0(X2_36,X1_36)) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_113,c_707]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_800,plain,
% 11.86/2.00      ( r1_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)),k4_xboole_0(k4_xboole_0(X2_36,X1_36),X1_36)) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_113,c_717]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_802,plain,
% 11.86/2.00      ( r1_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)),k4_xboole_0(X2_36,k2_xboole_0(X1_36,X1_36))) = iProver_top ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_800,c_112]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1,plain,
% 11.86/2.00      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f17]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_115,plain,
% 11.86/2.00      ( r2_hidden(sK0(X0_36,X1_36),X1_36) | r1_xboole_0(X0_36,X1_36) ),
% 11.86/2.00      inference(subtyping,[status(esa)],[c_1]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_288,plain,
% 11.86/2.00      ( r2_hidden(sK0(X0_36,X1_36),X1_36) = iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,X1_36) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_115]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_0,plain,
% 11.86/2.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f18]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_116,plain,
% 11.86/2.00      ( ~ r2_hidden(X0_37,X0_36)
% 11.86/2.00      | ~ r2_hidden(X0_37,X1_36)
% 11.86/2.00      | ~ r1_xboole_0(X0_36,X1_36) ),
% 11.86/2.00      inference(subtyping,[status(esa)],[c_0]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_287,plain,
% 11.86/2.00      ( r2_hidden(X0_37,X0_36) != iProver_top
% 11.86/2.00      | r2_hidden(X0_37,X1_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X1_36,X0_36) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_116]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_908,plain,
% 11.86/2.00      ( r2_hidden(sK0(X0_36,X1_36),X2_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X1_36,X2_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,X1_36) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_288,c_287]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2419,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,X0_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X1_36,X0_36) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_288,c_908]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4522,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,k4_xboole_0(X1_36,k2_xboole_0(X1_36,X1_36))) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_802,c_2419]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_708,plain,
% 11.86/2.00      ( k2_xboole_0(X0_36,k4_xboole_0(X1_36,k2_xboole_0(X2_36,X0_36))) = k2_xboole_0(X0_36,k4_xboole_0(X1_36,X2_36)) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_112,c_113]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_7,plain,
% 11.86/2.00      ( ~ r1_xboole_0(X0,X1)
% 11.86/2.00      | ~ r1_xboole_0(X0,X2)
% 11.86/2.00      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f21]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_109,plain,
% 11.86/2.00      ( ~ r1_xboole_0(X0_36,X1_36)
% 11.86/2.00      | ~ r1_xboole_0(X0_36,X2_36)
% 11.86/2.00      | r1_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)) ),
% 11.86/2.00      inference(subtyping,[status(esa)],[c_7]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_292,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,X1_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,X2_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_109]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1584,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,X1_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,k4_xboole_0(X2_36,k2_xboole_0(X3_36,X1_36))) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,k2_xboole_0(X1_36,k4_xboole_0(X2_36,X3_36))) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_708,c_292]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_18655,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,X1_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,k2_xboole_0(X1_36,k4_xboole_0(X1_36,X1_36))) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_4522,c_1584]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_18725,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,X1_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,k2_xboole_0(X1_36,X1_36)) = iProver_top ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_18655,c_113]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2,plain,
% 11.86/2.00      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 11.86/2.00      inference(cnf_transformation,[],[f16]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_114,plain,
% 11.86/2.00      ( r2_hidden(sK0(X0_36,X1_36),X0_36) | r1_xboole_0(X0_36,X1_36) ),
% 11.86/2.00      inference(subtyping,[status(esa)],[c_2]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_289,plain,
% 11.86/2.00      ( r2_hidden(sK0(X0_36,X1_36),X0_36) = iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,X1_36) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_114]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_998,plain,
% 11.86/2.00      ( r2_hidden(sK0(X0_36,X1_36),X2_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,X2_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,X1_36) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_289,c_287]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_4006,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,X0_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,X1_36) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_289,c_998]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_19134,plain,
% 11.86/2.00      ( r1_xboole_0(k2_xboole_0(X0_36,X0_36),X0_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(k2_xboole_0(X0_36,X0_36),X1_36) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_18725,c_4006]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_20564,plain,
% 11.86/2.00      ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X0_36,X0_36)),k4_xboole_0(X0_36,k2_xboole_0(X0_36,X0_36))),X1_36) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_4522,c_19134]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_1001,plain,
% 11.86/2.00      ( k2_xboole_0(k4_xboole_0(X0_36,X1_36),k4_xboole_0(X2_36,k2_xboole_0(X1_36,X0_36))) = k2_xboole_0(k4_xboole_0(X0_36,X1_36),k4_xboole_0(X2_36,X1_36)) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_113,c_708]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2544,plain,
% 11.86/2.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0_36,X1_36),X1_36),k4_xboole_0(X2_36,k2_xboole_0(X1_36,X0_36))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0_36,X1_36),X1_36),k4_xboole_0(X2_36,X1_36)) ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_113,c_1001]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_2605,plain,
% 11.86/2.00      ( k2_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X1_36)),k4_xboole_0(X2_36,k2_xboole_0(X1_36,X0_36))) = k2_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X1_36,X1_36)),k4_xboole_0(X2_36,X1_36)) ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_2544,c_112]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_20579,plain,
% 11.86/2.00      ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X0_36,k2_xboole_0(X0_36,X0_36)),k4_xboole_0(X0_36,X0_36)),X1_36) = iProver_top ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_20564,c_2605]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_20626,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,k2_xboole_0(k4_xboole_0(X1_36,k2_xboole_0(X1_36,X1_36)),k4_xboole_0(X1_36,X1_36))) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_20579,c_2419]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_5,plain,
% 11.86/2.00      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f23]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_111,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,X1_36)
% 11.86/2.00      | ~ r1_xboole_0(X0_36,k2_xboole_0(X2_36,X1_36)) ),
% 11.86/2.00      inference(subtyping,[status(esa)],[c_5]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_290,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,X1_36) = iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,k2_xboole_0(X2_36,X1_36)) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_111]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_20950,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,k4_xboole_0(X1_36,X1_36)) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_20626,c_290]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_20989,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,k4_xboole_0(X1_36,k2_xboole_0(X2_36,k4_xboole_0(X1_36,X2_36)))) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_112,c_20950]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_20999,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,k4_xboole_0(X1_36,k2_xboole_0(X2_36,X1_36))) = iProver_top ),
% 11.86/2.00      inference(demodulation,[status(thm)],[c_20989,c_113]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_22103,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,X1_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,k2_xboole_0(X1_36,k4_xboole_0(X1_36,X2_36))) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_20999,c_1584]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_42781,plain,
% 11.86/2.00      ( r1_xboole_0(X0_36,X1_36) != iProver_top
% 11.86/2.00      | r1_xboole_0(X0_36,k4_xboole_0(X1_36,X2_36)) = iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_22103,c_290]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_9,negated_conjecture,
% 11.86/2.00      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) ),
% 11.86/2.00      inference(cnf_transformation,[],[f26]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_107,negated_conjecture,
% 11.86/2.00      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) ),
% 11.86/2.00      inference(subtyping,[status(esa)],[c_9]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_294,plain,
% 11.86/2.00      ( r1_xboole_0(sK1,k4_xboole_0(sK2,sK3)) != iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_107]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_42818,plain,
% 11.86/2.00      ( r1_xboole_0(sK1,sK2) != iProver_top ),
% 11.86/2.00      inference(superposition,[status(thm)],[c_42781,c_294]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_10,negated_conjecture,
% 11.86/2.00      ( r1_xboole_0(sK1,sK2) ),
% 11.86/2.00      inference(cnf_transformation,[],[f25]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(c_11,plain,
% 11.86/2.00      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 11.86/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.86/2.00  
% 11.86/2.00  cnf(contradiction,plain,
% 11.86/2.00      ( $false ),
% 11.86/2.00      inference(minisat,[status(thm)],[c_42818,c_11]) ).
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.86/2.00  
% 11.86/2.00  ------                               Statistics
% 11.86/2.00  
% 11.86/2.00  ------ General
% 11.86/2.00  
% 11.86/2.00  abstr_ref_over_cycles:                  0
% 11.86/2.00  abstr_ref_under_cycles:                 0
% 11.86/2.00  gc_basic_clause_elim:                   0
% 11.86/2.00  forced_gc_time:                         0
% 11.86/2.00  parsing_time:                           0.008
% 11.86/2.00  unif_index_cands_time:                  0.
% 11.86/2.00  unif_index_add_time:                    0.
% 11.86/2.00  orderings_time:                         0.
% 11.86/2.00  out_proof_time:                         0.009
% 11.86/2.00  total_time:                             1.276
% 11.86/2.00  num_of_symbols:                         41
% 11.86/2.00  num_of_terms:                           66806
% 11.86/2.00  
% 11.86/2.00  ------ Preprocessing
% 11.86/2.00  
% 11.86/2.00  num_of_splits:                          0
% 11.86/2.00  num_of_split_atoms:                     0
% 11.86/2.00  num_of_reused_defs:                     0
% 11.86/2.00  num_eq_ax_congr_red:                    8
% 11.86/2.00  num_of_sem_filtered_clauses:            1
% 11.86/2.00  num_of_subtypes:                        2
% 11.86/2.00  monotx_restored_types:                  0
% 11.86/2.00  sat_num_of_epr_types:                   0
% 11.86/2.00  sat_num_of_non_cyclic_types:            0
% 11.86/2.00  sat_guarded_non_collapsed_types:        0
% 11.86/2.00  num_pure_diseq_elim:                    0
% 11.86/2.00  simp_replaced_by:                       0
% 11.86/2.00  res_preprocessed:                       48
% 11.86/2.00  prep_upred:                             0
% 11.86/2.00  prep_unflattend:                        0
% 11.86/2.00  smt_new_axioms:                         0
% 11.86/2.00  pred_elim_cands:                        2
% 11.86/2.00  pred_elim:                              0
% 11.86/2.00  pred_elim_cl:                           0
% 11.86/2.00  pred_elim_cycles:                       1
% 11.86/2.00  merged_defs:                            0
% 11.86/2.00  merged_defs_ncl:                        0
% 11.86/2.00  bin_hyper_res:                          0
% 11.86/2.00  prep_cycles:                            3
% 11.86/2.00  pred_elim_time:                         0.
% 11.86/2.00  splitting_time:                         0.
% 11.86/2.00  sem_filter_time:                        0.
% 11.86/2.00  monotx_time:                            0.
% 11.86/2.00  subtype_inf_time:                       0.
% 11.86/2.00  
% 11.86/2.00  ------ Problem properties
% 11.86/2.00  
% 11.86/2.00  clauses:                                11
% 11.86/2.00  conjectures:                            2
% 11.86/2.00  epr:                                    2
% 11.86/2.00  horn:                                   9
% 11.86/2.00  ground:                                 2
% 11.86/2.00  unary:                                  5
% 11.86/2.00  binary:                                 4
% 11.86/2.00  lits:                                   19
% 11.86/2.00  lits_eq:                                2
% 11.86/2.00  fd_pure:                                0
% 11.86/2.00  fd_pseudo:                              0
% 11.86/2.00  fd_cond:                                0
% 11.86/2.00  fd_pseudo_cond:                         0
% 11.86/2.00  ac_symbols:                             0
% 11.86/2.00  
% 11.86/2.00  ------ Propositional Solver
% 11.86/2.00  
% 11.86/2.00  prop_solver_calls:                      28
% 11.86/2.00  prop_fast_solver_calls:                 488
% 11.86/2.00  smt_solver_calls:                       0
% 11.86/2.00  smt_fast_solver_calls:                  0
% 11.86/2.00  prop_num_of_clauses:                    18338
% 11.86/2.00  prop_preprocess_simplified:             23299
% 11.86/2.00  prop_fo_subsumed:                       1
% 11.86/2.00  prop_solver_time:                       0.
% 11.86/2.00  smt_solver_time:                        0.
% 11.86/2.00  smt_fast_solver_time:                   0.
% 11.86/2.00  prop_fast_solver_time:                  0.
% 11.86/2.00  prop_unsat_core_time:                   0.001
% 11.86/2.00  
% 11.86/2.00  ------ QBF
% 11.86/2.00  
% 11.86/2.00  qbf_q_res:                              0
% 11.86/2.00  qbf_num_tautologies:                    0
% 11.86/2.00  qbf_prep_cycles:                        0
% 11.86/2.00  
% 11.86/2.00  ------ BMC1
% 11.86/2.00  
% 11.86/2.00  bmc1_current_bound:                     -1
% 11.86/2.00  bmc1_last_solved_bound:                 -1
% 11.86/2.00  bmc1_unsat_core_size:                   -1
% 11.86/2.00  bmc1_unsat_core_parents_size:           -1
% 11.86/2.00  bmc1_merge_next_fun:                    0
% 11.86/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.86/2.00  
% 11.86/2.00  ------ Instantiation
% 11.86/2.00  
% 11.86/2.00  inst_num_of_clauses:                    3070
% 11.86/2.00  inst_num_in_passive:                    622
% 11.86/2.00  inst_num_in_active:                     1179
% 11.86/2.00  inst_num_in_unprocessed:                1297
% 11.86/2.00  inst_num_of_loops:                      1280
% 11.86/2.00  inst_num_of_learning_restarts:          0
% 11.86/2.00  inst_num_moves_active_passive:          100
% 11.86/2.00  inst_lit_activity:                      0
% 11.86/2.00  inst_lit_activity_moves:                0
% 11.86/2.00  inst_num_tautologies:                   0
% 11.86/2.00  inst_num_prop_implied:                  0
% 11.86/2.00  inst_num_existing_simplified:           0
% 11.86/2.00  inst_num_eq_res_simplified:             0
% 11.86/2.00  inst_num_child_elim:                    0
% 11.86/2.00  inst_num_of_dismatching_blockings:      7642
% 11.86/2.00  inst_num_of_non_proper_insts:           5035
% 11.86/2.00  inst_num_of_duplicates:                 0
% 11.86/2.00  inst_inst_num_from_inst_to_res:         0
% 11.86/2.00  inst_dismatching_checking_time:         0.
% 11.86/2.00  
% 11.86/2.00  ------ Resolution
% 11.86/2.00  
% 11.86/2.00  res_num_of_clauses:                     0
% 11.86/2.00  res_num_in_passive:                     0
% 11.86/2.00  res_num_in_active:                      0
% 11.86/2.00  res_num_of_loops:                       51
% 11.86/2.00  res_forward_subset_subsumed:            290
% 11.86/2.00  res_backward_subset_subsumed:           60
% 11.86/2.00  res_forward_subsumed:                   0
% 11.86/2.00  res_backward_subsumed:                  0
% 11.86/2.00  res_forward_subsumption_resolution:     0
% 11.86/2.00  res_backward_subsumption_resolution:    0
% 11.86/2.00  res_clause_to_clause_subsumption:       176967
% 11.86/2.00  res_orphan_elimination:                 0
% 11.86/2.00  res_tautology_del:                      142
% 11.86/2.00  res_num_eq_res_simplified:              0
% 11.86/2.00  res_num_sel_changes:                    0
% 11.86/2.00  res_moves_from_active_to_pass:          0
% 11.86/2.00  
% 11.86/2.00  ------ Superposition
% 11.86/2.00  
% 11.86/2.00  sup_time_total:                         0.
% 11.86/2.00  sup_time_generating:                    0.
% 11.86/2.00  sup_time_sim_full:                      0.
% 11.86/2.00  sup_time_sim_immed:                     0.
% 11.86/2.00  
% 11.86/2.00  sup_num_of_clauses:                     2861
% 11.86/2.00  sup_num_in_active:                      228
% 11.86/2.00  sup_num_in_passive:                     2633
% 11.86/2.00  sup_num_of_loops:                       255
% 11.86/2.00  sup_fw_superposition:                   3096
% 11.86/2.00  sup_bw_superposition:                   2277
% 11.86/2.00  sup_immediate_simplified:               2497
% 11.86/2.00  sup_given_eliminated:                   0
% 11.86/2.00  comparisons_done:                       0
% 11.86/2.00  comparisons_avoided:                    0
% 11.86/2.00  
% 11.86/2.00  ------ Simplifications
% 11.86/2.00  
% 11.86/2.00  
% 11.86/2.00  sim_fw_subset_subsumed:                 13
% 11.86/2.00  sim_bw_subset_subsumed:                 6
% 11.86/2.00  sim_fw_subsumed:                        653
% 11.86/2.00  sim_bw_subsumed:                        51
% 11.86/2.00  sim_fw_subsumption_res:                 0
% 11.86/2.00  sim_bw_subsumption_res:                 0
% 11.86/2.00  sim_tautology_del:                      8
% 11.86/2.00  sim_eq_tautology_del:                   27
% 11.86/2.00  sim_eq_res_simp:                        0
% 11.86/2.00  sim_fw_demodulated:                     2787
% 11.86/2.00  sim_bw_demodulated:                     23
% 11.86/2.00  sim_light_normalised:                   168
% 11.86/2.00  sim_joinable_taut:                      0
% 11.86/2.00  sim_joinable_simp:                      0
% 11.86/2.00  sim_ac_normalised:                      0
% 11.86/2.00  sim_smt_subsumption:                    0
% 11.86/2.00  
%------------------------------------------------------------------------------
