%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:28 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 911 expanded)
%              Number of clauses        :   50 ( 292 expanded)
%              Number of leaves         :   10 ( 225 expanded)
%              Depth                    :   22
%              Number of atoms          :  160 (2228 expanded)
%              Number of equality atoms :   95 ( 883 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ! [X5,X6,X7,X8] :
            ( k4_mcart_1(X5,X6,X7,X8) != X0
            | ~ r2_hidden(X8,X4)
            | ~ r2_hidden(X7,X3)
            | ~ r2_hidden(X6,X2)
            | ~ r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) )
   => ( ! [X8,X7,X6,X5] :
          ( k4_mcart_1(X5,X6,X7,X8) != sK2
          | ~ r2_hidden(X8,sK6)
          | ~ r2_hidden(X7,sK5)
          | ~ r2_hidden(X6,sK4)
          | ~ r2_hidden(X5,sK3) )
      & r2_hidden(sK2,k4_zfmisc_1(sK3,sK4,sK5,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ! [X5,X6,X7,X8] :
        ( k4_mcart_1(X5,X6,X7,X8) != sK2
        | ~ r2_hidden(X8,sK6)
        | ~ r2_hidden(X7,sK5)
        | ~ r2_hidden(X6,sK4)
        | ~ r2_hidden(X5,sK3) )
    & r2_hidden(sK2,k4_zfmisc_1(sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f12,f15])).

fof(f26,plain,(
    r2_hidden(sK2,k4_zfmisc_1(sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f31,plain,(
    r2_hidden(sK2,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6)) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK0(X0),sK1(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK0(X0),sK1(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK0(X0),sK1(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f19])).

fof(f27,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_mcart_1(X5,X6,X7,X8) != sK2
      | ~ r2_hidden(X8,sK6)
      | ~ r2_hidden(X7,sK5)
      | ~ r2_hidden(X6,sK4)
      | ~ r2_hidden(X5,sK3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X6,X8,X7,X5] :
      ( k4_tarski(k3_mcart_1(X5,X6,X7),X8) != sK2
      | ~ r2_hidden(X8,sK6)
      | ~ r2_hidden(X7,sK5)
      | ~ r2_hidden(X6,sK4)
      | ~ r2_hidden(X5,sK3) ) ),
    inference(definition_unfolding,[],[f27,f19])).

fof(f25,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_7,negated_conjecture,
    ( r2_hidden(sK2,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_174,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_178,plain,
    ( k4_tarski(sK0(X0),sK1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_678,plain,
    ( k4_tarski(sK0(sK2),sK1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_174,c_178])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_176,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_555,plain,
    ( r2_hidden(k1_mcart_1(sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_174,c_176])).

cnf(c_906,plain,
    ( k4_tarski(sK0(k1_mcart_1(sK2)),sK1(k1_mcart_1(sK2))) = k1_mcart_1(sK2) ),
    inference(superposition,[status(thm)],[c_555,c_178])).

cnf(c_5,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_895,plain,
    ( k1_mcart_1(sK2) = sK0(sK2) ),
    inference(superposition,[status(thm)],[c_678,c_5])).

cnf(c_1254,plain,
    ( k4_tarski(sK0(sK0(sK2)),sK1(sK0(sK2))) = sK0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_906,c_895])).

cnf(c_3,plain,
    ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_397,plain,
    ( k1_mcart_1(k4_tarski(k3_mcart_1(X0,X1,X2),X3)) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_404,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_397,c_5])).

cnf(c_1256,plain,
    ( k3_mcart_1(sK0(sK0(sK2)),sK1(sK0(sK2)),X0) = k4_tarski(sK0(sK2),X0) ),
    inference(superposition,[status(thm)],[c_1254,c_404])).

cnf(c_1257,plain,
    ( k1_mcart_1(sK0(sK2)) = sK0(sK0(sK2)) ),
    inference(superposition,[status(thm)],[c_1254,c_5])).

cnf(c_908,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK2)),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_176])).

cnf(c_1174,plain,
    ( r2_hidden(k1_mcart_1(sK0(sK2)),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_908,c_895])).

cnf(c_1383,plain,
    ( r2_hidden(sK0(sK0(sK2)),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1257,c_1174])).

cnf(c_1869,plain,
    ( k4_tarski(sK0(sK0(sK0(sK2))),sK1(sK0(sK0(sK2)))) = sK0(sK0(sK2)) ),
    inference(superposition,[status(thm)],[c_1383,c_178])).

cnf(c_2003,plain,
    ( k3_mcart_1(sK0(sK0(sK0(sK2))),sK1(sK0(sK0(sK2))),X0) = k4_tarski(sK0(sK0(sK2)),X0) ),
    inference(superposition,[status(thm)],[c_1869,c_404])).

cnf(c_6,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X1,sK4)
    | ~ r2_hidden(X2,sK5)
    | ~ r2_hidden(X3,sK6)
    | k4_tarski(k3_mcart_1(X0,X1,X2),X3) != sK2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_175,plain,
    ( k4_tarski(k3_mcart_1(X0,X1,X2),X3) != sK2
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK4) != iProver_top
    | r2_hidden(X2,sK5) != iProver_top
    | r2_hidden(X3,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2269,plain,
    ( k4_tarski(k4_tarski(sK0(sK0(sK2)),X0),X1) != sK2
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(sK1(sK0(sK0(sK2))),sK4) != iProver_top
    | r2_hidden(sK0(sK0(sK0(sK2))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_175])).

cnf(c_2275,plain,
    ( k3_mcart_1(sK0(sK0(sK2)),X0,X1) != sK2
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(sK1(sK0(sK0(sK2))),sK4) != iProver_top
    | r2_hidden(sK0(sK0(sK0(sK2))),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2269,c_404])).

cnf(c_2004,plain,
    ( k1_mcart_1(sK0(sK0(sK2))) = sK0(sK0(sK0(sK2))) ),
    inference(superposition,[status(thm)],[c_1869,c_5])).

cnf(c_1179,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK0(sK2))),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_176])).

cnf(c_1810,plain,
    ( r2_hidden(k1_mcart_1(sK0(sK0(sK2))),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1179,c_1257])).

cnf(c_2070,plain,
    ( r2_hidden(sK0(sK0(sK0(sK2))),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2004,c_1810])).

cnf(c_4,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2005,plain,
    ( k2_mcart_1(sK0(sK0(sK2))) = sK1(sK0(sK0(sK2))) ),
    inference(superposition,[status(thm)],[c_1869,c_4])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_177,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1178,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK0(sK2))),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_177])).

cnf(c_1515,plain,
    ( r2_hidden(k2_mcart_1(sK0(sK0(sK2))),sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1178,c_1257])).

cnf(c_2073,plain,
    ( r2_hidden(sK1(sK0(sK0(sK2))),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2005,c_1515])).

cnf(c_2376,plain,
    ( k3_mcart_1(sK0(sK0(sK2)),X0,X1) != sK2
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2275,c_2070,c_2073])).

cnf(c_2385,plain,
    ( k4_tarski(sK0(sK2),X0) != sK2
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK1(sK0(sK2)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_2376])).

cnf(c_1258,plain,
    ( k2_mcart_1(sK0(sK2)) = sK1(sK0(sK2)) ),
    inference(superposition,[status(thm)],[c_1254,c_4])).

cnf(c_907,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK2)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_177])).

cnf(c_1081,plain,
    ( r2_hidden(k2_mcart_1(sK0(sK2)),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_907,c_895])).

cnf(c_1386,plain,
    ( r2_hidden(sK1(sK0(sK2)),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1258,c_1081])).

cnf(c_2390,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | k4_tarski(sK0(sK2),X0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2385,c_1386])).

cnf(c_2391,plain,
    ( k4_tarski(sK0(sK2),X0) != sK2
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_2390])).

cnf(c_2398,plain,
    ( r2_hidden(sK1(sK2),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_2391])).

cnf(c_896,plain,
    ( k2_mcart_1(sK2) = sK1(sK2) ),
    inference(superposition,[status(thm)],[c_678,c_4])).

cnf(c_560,plain,
    ( r2_hidden(k2_mcart_1(sK2),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_174,c_177])).

cnf(c_1015,plain,
    ( r2_hidden(sK1(sK2),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_896,c_560])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2398,c_1015])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:10:27 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 1.98/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/0.98  
% 1.98/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.98/0.98  
% 1.98/0.98  ------  iProver source info
% 1.98/0.98  
% 1.98/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.98/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.98/0.98  git: non_committed_changes: false
% 1.98/0.98  git: last_make_outside_of_git: false
% 1.98/0.98  
% 1.98/0.98  ------ 
% 1.98/0.98  
% 1.98/0.98  ------ Input Options
% 1.98/0.98  
% 1.98/0.98  --out_options                           all
% 1.98/0.98  --tptp_safe_out                         true
% 1.98/0.98  --problem_path                          ""
% 1.98/0.98  --include_path                          ""
% 1.98/0.98  --clausifier                            res/vclausify_rel
% 1.98/0.98  --clausifier_options                    --mode clausify
% 1.98/0.98  --stdin                                 false
% 1.98/0.98  --stats_out                             all
% 1.98/0.98  
% 1.98/0.98  ------ General Options
% 1.98/0.98  
% 1.98/0.98  --fof                                   false
% 1.98/0.98  --time_out_real                         305.
% 1.98/0.98  --time_out_virtual                      -1.
% 1.98/0.98  --symbol_type_check                     false
% 1.98/0.98  --clausify_out                          false
% 1.98/0.98  --sig_cnt_out                           false
% 1.98/0.98  --trig_cnt_out                          false
% 1.98/0.98  --trig_cnt_out_tolerance                1.
% 1.98/0.98  --trig_cnt_out_sk_spl                   false
% 1.98/0.98  --abstr_cl_out                          false
% 1.98/0.98  
% 1.98/0.98  ------ Global Options
% 1.98/0.98  
% 1.98/0.98  --schedule                              default
% 1.98/0.98  --add_important_lit                     false
% 1.98/0.98  --prop_solver_per_cl                    1000
% 1.98/0.98  --min_unsat_core                        false
% 1.98/0.98  --soft_assumptions                      false
% 1.98/0.98  --soft_lemma_size                       3
% 1.98/0.98  --prop_impl_unit_size                   0
% 1.98/0.98  --prop_impl_unit                        []
% 1.98/0.98  --share_sel_clauses                     true
% 1.98/0.98  --reset_solvers                         false
% 1.98/0.98  --bc_imp_inh                            [conj_cone]
% 1.98/0.98  --conj_cone_tolerance                   3.
% 1.98/0.98  --extra_neg_conj                        none
% 1.98/0.98  --large_theory_mode                     true
% 1.98/0.98  --prolific_symb_bound                   200
% 1.98/0.98  --lt_threshold                          2000
% 1.98/0.98  --clause_weak_htbl                      true
% 1.98/0.98  --gc_record_bc_elim                     false
% 1.98/0.98  
% 1.98/0.98  ------ Preprocessing Options
% 1.98/0.98  
% 1.98/0.98  --preprocessing_flag                    true
% 1.98/0.98  --time_out_prep_mult                    0.1
% 1.98/0.98  --splitting_mode                        input
% 1.98/0.98  --splitting_grd                         true
% 1.98/0.98  --splitting_cvd                         false
% 1.98/0.98  --splitting_cvd_svl                     false
% 1.98/0.98  --splitting_nvd                         32
% 1.98/0.98  --sub_typing                            true
% 1.98/0.98  --prep_gs_sim                           true
% 1.98/0.98  --prep_unflatten                        true
% 1.98/0.98  --prep_res_sim                          true
% 1.98/0.98  --prep_upred                            true
% 1.98/0.98  --prep_sem_filter                       exhaustive
% 1.98/0.98  --prep_sem_filter_out                   false
% 1.98/0.98  --pred_elim                             true
% 1.98/0.98  --res_sim_input                         true
% 1.98/0.98  --eq_ax_congr_red                       true
% 1.98/0.98  --pure_diseq_elim                       true
% 1.98/0.98  --brand_transform                       false
% 1.98/0.98  --non_eq_to_eq                          false
% 1.98/0.98  --prep_def_merge                        true
% 1.98/0.98  --prep_def_merge_prop_impl              false
% 1.98/0.98  --prep_def_merge_mbd                    true
% 1.98/0.98  --prep_def_merge_tr_red                 false
% 1.98/0.98  --prep_def_merge_tr_cl                  false
% 1.98/0.98  --smt_preprocessing                     true
% 1.98/0.98  --smt_ac_axioms                         fast
% 1.98/0.98  --preprocessed_out                      false
% 1.98/0.98  --preprocessed_stats                    false
% 1.98/0.98  
% 1.98/0.98  ------ Abstraction refinement Options
% 1.98/0.98  
% 1.98/0.98  --abstr_ref                             []
% 1.98/0.98  --abstr_ref_prep                        false
% 1.98/0.98  --abstr_ref_until_sat                   false
% 1.98/0.98  --abstr_ref_sig_restrict                funpre
% 1.98/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.98/0.98  --abstr_ref_under                       []
% 1.98/0.98  
% 1.98/0.98  ------ SAT Options
% 1.98/0.98  
% 1.98/0.98  --sat_mode                              false
% 1.98/0.98  --sat_fm_restart_options                ""
% 1.98/0.98  --sat_gr_def                            false
% 1.98/0.98  --sat_epr_types                         true
% 1.98/0.98  --sat_non_cyclic_types                  false
% 1.98/0.98  --sat_finite_models                     false
% 1.98/0.98  --sat_fm_lemmas                         false
% 1.98/0.98  --sat_fm_prep                           false
% 1.98/0.98  --sat_fm_uc_incr                        true
% 1.98/0.98  --sat_out_model                         small
% 1.98/0.98  --sat_out_clauses                       false
% 1.98/0.98  
% 1.98/0.98  ------ QBF Options
% 1.98/0.98  
% 1.98/0.98  --qbf_mode                              false
% 1.98/0.98  --qbf_elim_univ                         false
% 1.98/0.98  --qbf_dom_inst                          none
% 1.98/0.98  --qbf_dom_pre_inst                      false
% 1.98/0.98  --qbf_sk_in                             false
% 1.98/0.98  --qbf_pred_elim                         true
% 1.98/0.98  --qbf_split                             512
% 1.98/0.98  
% 1.98/0.98  ------ BMC1 Options
% 1.98/0.98  
% 1.98/0.98  --bmc1_incremental                      false
% 1.98/0.98  --bmc1_axioms                           reachable_all
% 1.98/0.98  --bmc1_min_bound                        0
% 1.98/0.98  --bmc1_max_bound                        -1
% 1.98/0.98  --bmc1_max_bound_default                -1
% 1.98/0.98  --bmc1_symbol_reachability              true
% 1.98/0.98  --bmc1_property_lemmas                  false
% 1.98/0.98  --bmc1_k_induction                      false
% 1.98/0.98  --bmc1_non_equiv_states                 false
% 1.98/0.98  --bmc1_deadlock                         false
% 1.98/0.98  --bmc1_ucm                              false
% 1.98/0.98  --bmc1_add_unsat_core                   none
% 1.98/0.98  --bmc1_unsat_core_children              false
% 1.98/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.98/0.98  --bmc1_out_stat                         full
% 1.98/0.98  --bmc1_ground_init                      false
% 1.98/0.98  --bmc1_pre_inst_next_state              false
% 1.98/0.98  --bmc1_pre_inst_state                   false
% 1.98/0.98  --bmc1_pre_inst_reach_state             false
% 1.98/0.98  --bmc1_out_unsat_core                   false
% 1.98/0.98  --bmc1_aig_witness_out                  false
% 1.98/0.98  --bmc1_verbose                          false
% 1.98/0.98  --bmc1_dump_clauses_tptp                false
% 1.98/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.98/0.98  --bmc1_dump_file                        -
% 1.98/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.98/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.98/0.98  --bmc1_ucm_extend_mode                  1
% 1.98/0.98  --bmc1_ucm_init_mode                    2
% 1.98/0.98  --bmc1_ucm_cone_mode                    none
% 1.98/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.98/0.98  --bmc1_ucm_relax_model                  4
% 1.98/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.98/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.98/0.98  --bmc1_ucm_layered_model                none
% 1.98/0.98  --bmc1_ucm_max_lemma_size               10
% 1.98/0.98  
% 1.98/0.98  ------ AIG Options
% 1.98/0.98  
% 1.98/0.98  --aig_mode                              false
% 1.98/0.98  
% 1.98/0.98  ------ Instantiation Options
% 1.98/0.98  
% 1.98/0.98  --instantiation_flag                    true
% 1.98/0.98  --inst_sos_flag                         false
% 1.98/0.98  --inst_sos_phase                        true
% 1.98/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.98/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.98/0.98  --inst_lit_sel_side                     num_symb
% 1.98/0.98  --inst_solver_per_active                1400
% 1.98/0.98  --inst_solver_calls_frac                1.
% 1.98/0.98  --inst_passive_queue_type               priority_queues
% 1.98/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.98/0.98  --inst_passive_queues_freq              [25;2]
% 1.98/0.98  --inst_dismatching                      true
% 1.98/0.98  --inst_eager_unprocessed_to_passive     true
% 1.98/0.98  --inst_prop_sim_given                   true
% 1.98/0.98  --inst_prop_sim_new                     false
% 1.98/0.98  --inst_subs_new                         false
% 1.98/0.98  --inst_eq_res_simp                      false
% 1.98/0.98  --inst_subs_given                       false
% 1.98/0.98  --inst_orphan_elimination               true
% 1.98/0.98  --inst_learning_loop_flag               true
% 1.98/0.98  --inst_learning_start                   3000
% 1.98/0.98  --inst_learning_factor                  2
% 1.98/0.98  --inst_start_prop_sim_after_learn       3
% 1.98/0.98  --inst_sel_renew                        solver
% 1.98/0.98  --inst_lit_activity_flag                true
% 1.98/0.98  --inst_restr_to_given                   false
% 1.98/0.98  --inst_activity_threshold               500
% 1.98/0.98  --inst_out_proof                        true
% 1.98/0.98  
% 1.98/0.98  ------ Resolution Options
% 1.98/0.98  
% 1.98/0.98  --resolution_flag                       true
% 1.98/0.98  --res_lit_sel                           adaptive
% 1.98/0.98  --res_lit_sel_side                      none
% 1.98/0.98  --res_ordering                          kbo
% 1.98/0.98  --res_to_prop_solver                    active
% 1.98/0.98  --res_prop_simpl_new                    false
% 1.98/0.98  --res_prop_simpl_given                  true
% 1.98/0.98  --res_passive_queue_type                priority_queues
% 1.98/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.98/0.98  --res_passive_queues_freq               [15;5]
% 1.98/0.98  --res_forward_subs                      full
% 1.98/0.98  --res_backward_subs                     full
% 1.98/0.98  --res_forward_subs_resolution           true
% 1.98/0.98  --res_backward_subs_resolution          true
% 1.98/0.98  --res_orphan_elimination                true
% 1.98/0.98  --res_time_limit                        2.
% 1.98/0.98  --res_out_proof                         true
% 1.98/0.98  
% 1.98/0.98  ------ Superposition Options
% 1.98/0.98  
% 1.98/0.98  --superposition_flag                    true
% 1.98/0.98  --sup_passive_queue_type                priority_queues
% 1.98/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.98/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.98/0.98  --demod_completeness_check              fast
% 1.98/0.98  --demod_use_ground                      true
% 1.98/0.98  --sup_to_prop_solver                    passive
% 1.98/0.98  --sup_prop_simpl_new                    true
% 1.98/0.98  --sup_prop_simpl_given                  true
% 1.98/0.98  --sup_fun_splitting                     false
% 1.98/0.98  --sup_smt_interval                      50000
% 1.98/0.98  
% 1.98/0.98  ------ Superposition Simplification Setup
% 1.98/0.98  
% 1.98/0.98  --sup_indices_passive                   []
% 1.98/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.98/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.98  --sup_full_bw                           [BwDemod]
% 1.98/0.98  --sup_immed_triv                        [TrivRules]
% 1.98/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.98/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.98  --sup_immed_bw_main                     []
% 1.98/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.98/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.98  
% 1.98/0.98  ------ Combination Options
% 1.98/0.98  
% 1.98/0.98  --comb_res_mult                         3
% 1.98/0.98  --comb_sup_mult                         2
% 1.98/0.98  --comb_inst_mult                        10
% 1.98/0.98  
% 1.98/0.98  ------ Debug Options
% 1.98/0.98  
% 1.98/0.98  --dbg_backtrace                         false
% 1.98/0.98  --dbg_dump_prop_clauses                 false
% 1.98/0.98  --dbg_dump_prop_clauses_file            -
% 1.98/0.98  --dbg_out_stat                          false
% 1.98/0.98  ------ Parsing...
% 1.98/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.98/0.98  
% 1.98/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.98/0.98  
% 1.98/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.98/0.98  
% 1.98/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.98/0.98  ------ Proving...
% 1.98/0.98  ------ Problem Properties 
% 1.98/0.98  
% 1.98/0.98  
% 1.98/0.98  clauses                                 8
% 1.98/0.98  conjectures                             2
% 1.98/0.98  EPR                                     0
% 1.98/0.98  Horn                                    8
% 1.98/0.98  unary                                   4
% 1.98/0.98  binary                                  3
% 1.98/0.98  lits                                    15
% 1.98/0.98  lits eq                                 5
% 1.98/0.98  fd_pure                                 0
% 1.98/0.98  fd_pseudo                               0
% 1.98/0.98  fd_cond                                 0
% 1.98/0.98  fd_pseudo_cond                          0
% 1.98/0.98  AC symbols                              0
% 1.98/0.98  
% 1.98/0.98  ------ Schedule dynamic 5 is on 
% 1.98/0.98  
% 1.98/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.98/0.98  
% 1.98/0.98  
% 1.98/0.98  ------ 
% 1.98/0.98  Current options:
% 1.98/0.98  ------ 
% 1.98/0.98  
% 1.98/0.98  ------ Input Options
% 1.98/0.98  
% 1.98/0.98  --out_options                           all
% 1.98/0.98  --tptp_safe_out                         true
% 1.98/0.98  --problem_path                          ""
% 1.98/0.98  --include_path                          ""
% 1.98/0.98  --clausifier                            res/vclausify_rel
% 1.98/0.98  --clausifier_options                    --mode clausify
% 1.98/0.98  --stdin                                 false
% 1.98/0.98  --stats_out                             all
% 1.98/0.98  
% 1.98/0.98  ------ General Options
% 1.98/0.98  
% 1.98/0.98  --fof                                   false
% 1.98/0.98  --time_out_real                         305.
% 1.98/0.98  --time_out_virtual                      -1.
% 1.98/0.98  --symbol_type_check                     false
% 1.98/0.98  --clausify_out                          false
% 1.98/0.98  --sig_cnt_out                           false
% 1.98/0.98  --trig_cnt_out                          false
% 1.98/0.98  --trig_cnt_out_tolerance                1.
% 1.98/0.98  --trig_cnt_out_sk_spl                   false
% 1.98/0.98  --abstr_cl_out                          false
% 1.98/0.98  
% 1.98/0.98  ------ Global Options
% 1.98/0.98  
% 1.98/0.98  --schedule                              default
% 1.98/0.98  --add_important_lit                     false
% 1.98/0.98  --prop_solver_per_cl                    1000
% 1.98/0.98  --min_unsat_core                        false
% 1.98/0.98  --soft_assumptions                      false
% 1.98/0.98  --soft_lemma_size                       3
% 1.98/0.98  --prop_impl_unit_size                   0
% 1.98/0.98  --prop_impl_unit                        []
% 1.98/0.98  --share_sel_clauses                     true
% 1.98/0.98  --reset_solvers                         false
% 1.98/0.98  --bc_imp_inh                            [conj_cone]
% 1.98/0.98  --conj_cone_tolerance                   3.
% 1.98/0.98  --extra_neg_conj                        none
% 1.98/0.98  --large_theory_mode                     true
% 1.98/0.98  --prolific_symb_bound                   200
% 1.98/0.98  --lt_threshold                          2000
% 1.98/0.98  --clause_weak_htbl                      true
% 1.98/0.98  --gc_record_bc_elim                     false
% 1.98/0.98  
% 1.98/0.98  ------ Preprocessing Options
% 1.98/0.98  
% 1.98/0.98  --preprocessing_flag                    true
% 1.98/0.98  --time_out_prep_mult                    0.1
% 1.98/0.98  --splitting_mode                        input
% 1.98/0.98  --splitting_grd                         true
% 1.98/0.98  --splitting_cvd                         false
% 1.98/0.98  --splitting_cvd_svl                     false
% 1.98/0.98  --splitting_nvd                         32
% 1.98/0.98  --sub_typing                            true
% 1.98/0.98  --prep_gs_sim                           true
% 1.98/0.98  --prep_unflatten                        true
% 1.98/0.98  --prep_res_sim                          true
% 1.98/0.98  --prep_upred                            true
% 1.98/0.98  --prep_sem_filter                       exhaustive
% 1.98/0.98  --prep_sem_filter_out                   false
% 1.98/0.98  --pred_elim                             true
% 1.98/0.98  --res_sim_input                         true
% 1.98/0.98  --eq_ax_congr_red                       true
% 1.98/0.98  --pure_diseq_elim                       true
% 1.98/0.98  --brand_transform                       false
% 1.98/0.98  --non_eq_to_eq                          false
% 1.98/0.98  --prep_def_merge                        true
% 1.98/0.98  --prep_def_merge_prop_impl              false
% 1.98/0.98  --prep_def_merge_mbd                    true
% 1.98/0.98  --prep_def_merge_tr_red                 false
% 1.98/0.98  --prep_def_merge_tr_cl                  false
% 1.98/0.98  --smt_preprocessing                     true
% 1.98/0.98  --smt_ac_axioms                         fast
% 1.98/0.98  --preprocessed_out                      false
% 1.98/0.98  --preprocessed_stats                    false
% 1.98/0.98  
% 1.98/0.98  ------ Abstraction refinement Options
% 1.98/0.98  
% 1.98/0.98  --abstr_ref                             []
% 1.98/0.98  --abstr_ref_prep                        false
% 1.98/0.98  --abstr_ref_until_sat                   false
% 1.98/0.98  --abstr_ref_sig_restrict                funpre
% 1.98/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.98/0.98  --abstr_ref_under                       []
% 1.98/0.98  
% 1.98/0.98  ------ SAT Options
% 1.98/0.98  
% 1.98/0.98  --sat_mode                              false
% 1.98/0.98  --sat_fm_restart_options                ""
% 1.98/0.98  --sat_gr_def                            false
% 1.98/0.98  --sat_epr_types                         true
% 1.98/0.98  --sat_non_cyclic_types                  false
% 1.98/0.98  --sat_finite_models                     false
% 1.98/0.98  --sat_fm_lemmas                         false
% 1.98/0.98  --sat_fm_prep                           false
% 1.98/0.98  --sat_fm_uc_incr                        true
% 1.98/0.98  --sat_out_model                         small
% 1.98/0.98  --sat_out_clauses                       false
% 1.98/0.98  
% 1.98/0.98  ------ QBF Options
% 1.98/0.98  
% 1.98/0.98  --qbf_mode                              false
% 1.98/0.98  --qbf_elim_univ                         false
% 1.98/0.98  --qbf_dom_inst                          none
% 1.98/0.98  --qbf_dom_pre_inst                      false
% 1.98/0.98  --qbf_sk_in                             false
% 1.98/0.98  --qbf_pred_elim                         true
% 1.98/0.98  --qbf_split                             512
% 1.98/0.98  
% 1.98/0.98  ------ BMC1 Options
% 1.98/0.98  
% 1.98/0.98  --bmc1_incremental                      false
% 1.98/0.98  --bmc1_axioms                           reachable_all
% 1.98/0.98  --bmc1_min_bound                        0
% 1.98/0.98  --bmc1_max_bound                        -1
% 1.98/0.98  --bmc1_max_bound_default                -1
% 1.98/0.98  --bmc1_symbol_reachability              true
% 1.98/0.98  --bmc1_property_lemmas                  false
% 1.98/0.98  --bmc1_k_induction                      false
% 1.98/0.98  --bmc1_non_equiv_states                 false
% 1.98/0.98  --bmc1_deadlock                         false
% 1.98/0.98  --bmc1_ucm                              false
% 1.98/0.98  --bmc1_add_unsat_core                   none
% 1.98/0.98  --bmc1_unsat_core_children              false
% 1.98/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.98/0.98  --bmc1_out_stat                         full
% 1.98/0.98  --bmc1_ground_init                      false
% 1.98/0.98  --bmc1_pre_inst_next_state              false
% 1.98/0.98  --bmc1_pre_inst_state                   false
% 1.98/0.98  --bmc1_pre_inst_reach_state             false
% 1.98/0.98  --bmc1_out_unsat_core                   false
% 1.98/0.98  --bmc1_aig_witness_out                  false
% 1.98/0.98  --bmc1_verbose                          false
% 1.98/0.98  --bmc1_dump_clauses_tptp                false
% 1.98/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.98/0.98  --bmc1_dump_file                        -
% 1.98/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.98/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.98/0.98  --bmc1_ucm_extend_mode                  1
% 1.98/0.98  --bmc1_ucm_init_mode                    2
% 1.98/0.98  --bmc1_ucm_cone_mode                    none
% 1.98/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.98/0.98  --bmc1_ucm_relax_model                  4
% 1.98/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.98/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.98/0.98  --bmc1_ucm_layered_model                none
% 1.98/0.98  --bmc1_ucm_max_lemma_size               10
% 1.98/0.98  
% 1.98/0.98  ------ AIG Options
% 1.98/0.98  
% 1.98/0.98  --aig_mode                              false
% 1.98/0.98  
% 1.98/0.98  ------ Instantiation Options
% 1.98/0.98  
% 1.98/0.98  --instantiation_flag                    true
% 1.98/0.98  --inst_sos_flag                         false
% 1.98/0.98  --inst_sos_phase                        true
% 1.98/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.98/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.98/0.98  --inst_lit_sel_side                     none
% 1.98/0.98  --inst_solver_per_active                1400
% 1.98/0.98  --inst_solver_calls_frac                1.
% 1.98/0.98  --inst_passive_queue_type               priority_queues
% 1.98/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.98/0.98  --inst_passive_queues_freq              [25;2]
% 1.98/0.98  --inst_dismatching                      true
% 1.98/0.98  --inst_eager_unprocessed_to_passive     true
% 1.98/0.98  --inst_prop_sim_given                   true
% 1.98/0.98  --inst_prop_sim_new                     false
% 1.98/0.98  --inst_subs_new                         false
% 1.98/0.98  --inst_eq_res_simp                      false
% 1.98/0.98  --inst_subs_given                       false
% 1.98/0.98  --inst_orphan_elimination               true
% 1.98/0.98  --inst_learning_loop_flag               true
% 1.98/0.98  --inst_learning_start                   3000
% 1.98/0.98  --inst_learning_factor                  2
% 1.98/0.98  --inst_start_prop_sim_after_learn       3
% 1.98/0.98  --inst_sel_renew                        solver
% 1.98/0.98  --inst_lit_activity_flag                true
% 1.98/0.98  --inst_restr_to_given                   false
% 1.98/0.98  --inst_activity_threshold               500
% 1.98/0.98  --inst_out_proof                        true
% 1.98/0.98  
% 1.98/0.98  ------ Resolution Options
% 1.98/0.98  
% 1.98/0.98  --resolution_flag                       false
% 1.98/0.98  --res_lit_sel                           adaptive
% 1.98/0.98  --res_lit_sel_side                      none
% 1.98/0.98  --res_ordering                          kbo
% 1.98/0.98  --res_to_prop_solver                    active
% 1.98/0.98  --res_prop_simpl_new                    false
% 1.98/0.98  --res_prop_simpl_given                  true
% 1.98/0.98  --res_passive_queue_type                priority_queues
% 1.98/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.98/0.98  --res_passive_queues_freq               [15;5]
% 1.98/0.98  --res_forward_subs                      full
% 1.98/0.98  --res_backward_subs                     full
% 1.98/0.98  --res_forward_subs_resolution           true
% 1.98/0.98  --res_backward_subs_resolution          true
% 1.98/0.98  --res_orphan_elimination                true
% 1.98/0.98  --res_time_limit                        2.
% 1.98/0.98  --res_out_proof                         true
% 1.98/0.98  
% 1.98/0.98  ------ Superposition Options
% 1.98/0.98  
% 1.98/0.98  --superposition_flag                    true
% 1.98/0.98  --sup_passive_queue_type                priority_queues
% 1.98/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.98/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.98/0.98  --demod_completeness_check              fast
% 1.98/0.98  --demod_use_ground                      true
% 1.98/0.98  --sup_to_prop_solver                    passive
% 1.98/0.98  --sup_prop_simpl_new                    true
% 1.98/0.98  --sup_prop_simpl_given                  true
% 1.98/0.98  --sup_fun_splitting                     false
% 1.98/0.98  --sup_smt_interval                      50000
% 1.98/0.98  
% 1.98/0.98  ------ Superposition Simplification Setup
% 1.98/0.98  
% 1.98/0.98  --sup_indices_passive                   []
% 1.98/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.98/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.98  --sup_full_bw                           [BwDemod]
% 1.98/0.98  --sup_immed_triv                        [TrivRules]
% 1.98/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.98/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.98  --sup_immed_bw_main                     []
% 1.98/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.98/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.98  
% 1.98/0.98  ------ Combination Options
% 1.98/0.98  
% 1.98/0.98  --comb_res_mult                         3
% 1.98/0.98  --comb_sup_mult                         2
% 1.98/0.98  --comb_inst_mult                        10
% 1.98/0.98  
% 1.98/0.98  ------ Debug Options
% 1.98/0.98  
% 1.98/0.98  --dbg_backtrace                         false
% 1.98/0.98  --dbg_dump_prop_clauses                 false
% 1.98/0.98  --dbg_dump_prop_clauses_file            -
% 1.98/0.98  --dbg_out_stat                          false
% 1.98/0.98  
% 1.98/0.98  
% 1.98/0.98  
% 1.98/0.98  
% 1.98/0.98  ------ Proving...
% 1.98/0.98  
% 1.98/0.98  
% 1.98/0.98  % SZS status Theorem for theBenchmark.p
% 1.98/0.98  
% 1.98/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.98/0.98  
% 1.98/0.98  fof(f8,conjecture,(
% 1.98/0.98    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 1.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.98  
% 1.98/0.98  fof(f9,negated_conjecture,(
% 1.98/0.98    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 1.98/0.98    inference(negated_conjecture,[],[f8])).
% 1.98/0.98  
% 1.98/0.98  fof(f12,plain,(
% 1.98/0.98    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 1.98/0.98    inference(ennf_transformation,[],[f9])).
% 1.98/0.98  
% 1.98/0.98  fof(f15,plain,(
% 1.98/0.98    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4))) => (! [X8,X7,X6,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK2 | ~r2_hidden(X8,sK6) | ~r2_hidden(X7,sK5) | ~r2_hidden(X6,sK4) | ~r2_hidden(X5,sK3)) & r2_hidden(sK2,k4_zfmisc_1(sK3,sK4,sK5,sK6)))),
% 1.98/0.98    introduced(choice_axiom,[])).
% 1.98/0.98  
% 1.98/0.98  fof(f16,plain,(
% 1.98/0.98    ! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != sK2 | ~r2_hidden(X8,sK6) | ~r2_hidden(X7,sK5) | ~r2_hidden(X6,sK4) | ~r2_hidden(X5,sK3)) & r2_hidden(sK2,k4_zfmisc_1(sK3,sK4,sK5,sK6))),
% 1.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f12,f15])).
% 1.98/0.98  
% 1.98/0.98  fof(f26,plain,(
% 1.98/0.98    r2_hidden(sK2,k4_zfmisc_1(sK3,sK4,sK5,sK6))),
% 1.98/0.98    inference(cnf_transformation,[],[f16])).
% 1.98/0.98  
% 1.98/0.98  fof(f4,axiom,(
% 1.98/0.98    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 1.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.98  
% 1.98/0.98  fof(f20,plain,(
% 1.98/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.98/0.98    inference(cnf_transformation,[],[f4])).
% 1.98/0.98  
% 1.98/0.98  fof(f2,axiom,(
% 1.98/0.98    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 1.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.98  
% 1.98/0.98  fof(f18,plain,(
% 1.98/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 1.98/0.98    inference(cnf_transformation,[],[f2])).
% 1.98/0.98  
% 1.98/0.98  fof(f28,plain,(
% 1.98/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 1.98/0.98    inference(definition_unfolding,[],[f20,f18])).
% 1.98/0.98  
% 1.98/0.98  fof(f31,plain,(
% 1.98/0.98    r2_hidden(sK2,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6))),
% 1.98/0.98    inference(definition_unfolding,[],[f26,f28])).
% 1.98/0.98  
% 1.98/0.98  fof(f1,axiom,(
% 1.98/0.98    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.98  
% 1.98/0.98  fof(f10,plain,(
% 1.98/0.98    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.98/0.98    inference(ennf_transformation,[],[f1])).
% 1.98/0.98  
% 1.98/0.98  fof(f13,plain,(
% 1.98/0.98    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK0(X0),sK1(X0)) = X0)),
% 1.98/0.98    introduced(choice_axiom,[])).
% 1.98/0.98  
% 1.98/0.98  fof(f14,plain,(
% 1.98/0.98    ! [X0,X1,X2] : (k4_tarski(sK0(X0),sK1(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).
% 1.98/0.98  
% 1.98/0.98  fof(f17,plain,(
% 1.98/0.98    ( ! [X2,X0,X1] : (k4_tarski(sK0(X0),sK1(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.98/0.98    inference(cnf_transformation,[],[f14])).
% 1.98/0.98  
% 1.98/0.98  fof(f5,axiom,(
% 1.98/0.98    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.98  
% 1.98/0.98  fof(f11,plain,(
% 1.98/0.98    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.98/0.98    inference(ennf_transformation,[],[f5])).
% 1.98/0.98  
% 1.98/0.98  fof(f21,plain,(
% 1.98/0.98    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.98/0.98    inference(cnf_transformation,[],[f11])).
% 1.98/0.98  
% 1.98/0.98  fof(f7,axiom,(
% 1.98/0.98    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.98/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.98  
% 1.98/0.98  fof(f24,plain,(
% 1.98/0.98    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.98/0.98    inference(cnf_transformation,[],[f7])).
% 1.98/0.99  
% 1.98/0.99  fof(f6,axiom,(
% 1.98/0.99    ! [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f23,plain,(
% 1.98/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f6])).
% 1.98/0.99  
% 1.98/0.99  fof(f3,axiom,(
% 1.98/0.99    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)),
% 1.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.99  
% 1.98/0.99  fof(f19,plain,(
% 1.98/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f3])).
% 1.98/0.99  
% 1.98/0.99  fof(f29,plain,(
% 1.98/0.99    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 1.98/0.99    inference(definition_unfolding,[],[f23,f19])).
% 1.98/0.99  
% 1.98/0.99  fof(f27,plain,(
% 1.98/0.99    ( ! [X6,X8,X7,X5] : (k4_mcart_1(X5,X6,X7,X8) != sK2 | ~r2_hidden(X8,sK6) | ~r2_hidden(X7,sK5) | ~r2_hidden(X6,sK4) | ~r2_hidden(X5,sK3)) )),
% 1.98/0.99    inference(cnf_transformation,[],[f16])).
% 1.98/0.99  
% 1.98/0.99  fof(f30,plain,(
% 1.98/0.99    ( ! [X6,X8,X7,X5] : (k4_tarski(k3_mcart_1(X5,X6,X7),X8) != sK2 | ~r2_hidden(X8,sK6) | ~r2_hidden(X7,sK5) | ~r2_hidden(X6,sK4) | ~r2_hidden(X5,sK3)) )),
% 1.98/0.99    inference(definition_unfolding,[],[f27,f19])).
% 1.98/0.99  
% 1.98/0.99  fof(f25,plain,(
% 1.98/0.99    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.98/0.99    inference(cnf_transformation,[],[f7])).
% 1.98/0.99  
% 1.98/0.99  fof(f22,plain,(
% 1.98/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 1.98/0.99    inference(cnf_transformation,[],[f11])).
% 1.98/0.99  
% 1.98/0.99  cnf(c_7,negated_conjecture,
% 1.98/0.99      ( r2_hidden(sK2,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6)) ),
% 1.98/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_174,plain,
% 1.98/0.99      ( r2_hidden(sK2,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5),sK6)) = iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_0,plain,
% 1.98/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 1.98/0.99      | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
% 1.98/0.99      inference(cnf_transformation,[],[f17]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_178,plain,
% 1.98/0.99      ( k4_tarski(sK0(X0),sK1(X0)) = X0
% 1.98/0.99      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_678,plain,
% 1.98/0.99      ( k4_tarski(sK0(sK2),sK1(sK2)) = sK2 ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_174,c_178]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2,plain,
% 1.98/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 1.98/0.99      | r2_hidden(k1_mcart_1(X0),X1) ),
% 1.98/0.99      inference(cnf_transformation,[],[f21]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_176,plain,
% 1.98/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 1.98/0.99      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_555,plain,
% 1.98/0.99      ( r2_hidden(k1_mcart_1(sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_174,c_176]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_906,plain,
% 1.98/0.99      ( k4_tarski(sK0(k1_mcart_1(sK2)),sK1(k1_mcart_1(sK2))) = k1_mcart_1(sK2) ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_555,c_178]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_5,plain,
% 1.98/0.99      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 1.98/0.99      inference(cnf_transformation,[],[f24]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_895,plain,
% 1.98/0.99      ( k1_mcart_1(sK2) = sK0(sK2) ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_678,c_5]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1254,plain,
% 1.98/0.99      ( k4_tarski(sK0(sK0(sK2)),sK1(sK0(sK2))) = sK0(sK2) ),
% 1.98/0.99      inference(light_normalisation,[status(thm)],[c_906,c_895]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_3,plain,
% 1.98/0.99      ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
% 1.98/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_397,plain,
% 1.98/0.99      ( k1_mcart_1(k4_tarski(k3_mcart_1(X0,X1,X2),X3)) = k4_tarski(k4_tarski(X0,X1),X2) ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_404,plain,
% 1.98/0.99      ( k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
% 1.98/0.99      inference(demodulation,[status(thm)],[c_397,c_5]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1256,plain,
% 1.98/0.99      ( k3_mcart_1(sK0(sK0(sK2)),sK1(sK0(sK2)),X0) = k4_tarski(sK0(sK2),X0) ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_1254,c_404]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1257,plain,
% 1.98/0.99      ( k1_mcart_1(sK0(sK2)) = sK0(sK0(sK2)) ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_1254,c_5]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_908,plain,
% 1.98/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK2)),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_555,c_176]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1174,plain,
% 1.98/0.99      ( r2_hidden(k1_mcart_1(sK0(sK2)),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 1.98/0.99      inference(light_normalisation,[status(thm)],[c_908,c_895]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1383,plain,
% 1.98/0.99      ( r2_hidden(sK0(sK0(sK2)),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 1.98/0.99      inference(demodulation,[status(thm)],[c_1257,c_1174]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1869,plain,
% 1.98/0.99      ( k4_tarski(sK0(sK0(sK0(sK2))),sK1(sK0(sK0(sK2)))) = sK0(sK0(sK2)) ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_1383,c_178]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2003,plain,
% 1.98/0.99      ( k3_mcart_1(sK0(sK0(sK0(sK2))),sK1(sK0(sK0(sK2))),X0) = k4_tarski(sK0(sK0(sK2)),X0) ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_1869,c_404]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_6,negated_conjecture,
% 1.98/0.99      ( ~ r2_hidden(X0,sK3)
% 1.98/0.99      | ~ r2_hidden(X1,sK4)
% 1.98/0.99      | ~ r2_hidden(X2,sK5)
% 1.98/0.99      | ~ r2_hidden(X3,sK6)
% 1.98/0.99      | k4_tarski(k3_mcart_1(X0,X1,X2),X3) != sK2 ),
% 1.98/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_175,plain,
% 1.98/0.99      ( k4_tarski(k3_mcart_1(X0,X1,X2),X3) != sK2
% 1.98/0.99      | r2_hidden(X0,sK3) != iProver_top
% 1.98/0.99      | r2_hidden(X1,sK4) != iProver_top
% 1.98/0.99      | r2_hidden(X2,sK5) != iProver_top
% 1.98/0.99      | r2_hidden(X3,sK6) != iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2269,plain,
% 1.98/0.99      ( k4_tarski(k4_tarski(sK0(sK0(sK2)),X0),X1) != sK2
% 1.98/0.99      | r2_hidden(X0,sK5) != iProver_top
% 1.98/0.99      | r2_hidden(X1,sK6) != iProver_top
% 1.98/0.99      | r2_hidden(sK1(sK0(sK0(sK2))),sK4) != iProver_top
% 1.98/0.99      | r2_hidden(sK0(sK0(sK0(sK2))),sK3) != iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_2003,c_175]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2275,plain,
% 1.98/0.99      ( k3_mcart_1(sK0(sK0(sK2)),X0,X1) != sK2
% 1.98/0.99      | r2_hidden(X0,sK5) != iProver_top
% 1.98/0.99      | r2_hidden(X1,sK6) != iProver_top
% 1.98/0.99      | r2_hidden(sK1(sK0(sK0(sK2))),sK4) != iProver_top
% 1.98/0.99      | r2_hidden(sK0(sK0(sK0(sK2))),sK3) != iProver_top ),
% 1.98/0.99      inference(demodulation,[status(thm)],[c_2269,c_404]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2004,plain,
% 1.98/0.99      ( k1_mcart_1(sK0(sK0(sK2))) = sK0(sK0(sK0(sK2))) ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_1869,c_5]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1179,plain,
% 1.98/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK0(sK2))),sK3) = iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_1174,c_176]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1810,plain,
% 1.98/0.99      ( r2_hidden(k1_mcart_1(sK0(sK0(sK2))),sK3) = iProver_top ),
% 1.98/0.99      inference(light_normalisation,[status(thm)],[c_1179,c_1257]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2070,plain,
% 1.98/0.99      ( r2_hidden(sK0(sK0(sK0(sK2))),sK3) = iProver_top ),
% 1.98/0.99      inference(demodulation,[status(thm)],[c_2004,c_1810]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_4,plain,
% 1.98/0.99      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 1.98/0.99      inference(cnf_transformation,[],[f25]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2005,plain,
% 1.98/0.99      ( k2_mcart_1(sK0(sK0(sK2))) = sK1(sK0(sK0(sK2))) ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_1869,c_4]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1,plain,
% 1.98/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 1.98/0.99      | r2_hidden(k2_mcart_1(X0),X2) ),
% 1.98/0.99      inference(cnf_transformation,[],[f22]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_177,plain,
% 1.98/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 1.98/0.99      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 1.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1178,plain,
% 1.98/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK0(sK2))),sK4) = iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_1174,c_177]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1515,plain,
% 1.98/0.99      ( r2_hidden(k2_mcart_1(sK0(sK0(sK2))),sK4) = iProver_top ),
% 1.98/0.99      inference(light_normalisation,[status(thm)],[c_1178,c_1257]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2073,plain,
% 1.98/0.99      ( r2_hidden(sK1(sK0(sK0(sK2))),sK4) = iProver_top ),
% 1.98/0.99      inference(demodulation,[status(thm)],[c_2005,c_1515]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2376,plain,
% 1.98/0.99      ( k3_mcart_1(sK0(sK0(sK2)),X0,X1) != sK2
% 1.98/0.99      | r2_hidden(X0,sK5) != iProver_top
% 1.98/0.99      | r2_hidden(X1,sK6) != iProver_top ),
% 1.98/0.99      inference(global_propositional_subsumption,
% 1.98/0.99                [status(thm)],
% 1.98/0.99                [c_2275,c_2070,c_2073]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2385,plain,
% 1.98/0.99      ( k4_tarski(sK0(sK2),X0) != sK2
% 1.98/0.99      | r2_hidden(X0,sK6) != iProver_top
% 1.98/0.99      | r2_hidden(sK1(sK0(sK2)),sK5) != iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_1256,c_2376]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1258,plain,
% 1.98/0.99      ( k2_mcart_1(sK0(sK2)) = sK1(sK0(sK2)) ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_1254,c_4]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_907,plain,
% 1.98/0.99      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK2)),sK5) = iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_555,c_177]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1081,plain,
% 1.98/0.99      ( r2_hidden(k2_mcart_1(sK0(sK2)),sK5) = iProver_top ),
% 1.98/0.99      inference(light_normalisation,[status(thm)],[c_907,c_895]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1386,plain,
% 1.98/0.99      ( r2_hidden(sK1(sK0(sK2)),sK5) = iProver_top ),
% 1.98/0.99      inference(demodulation,[status(thm)],[c_1258,c_1081]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2390,plain,
% 1.98/0.99      ( r2_hidden(X0,sK6) != iProver_top
% 1.98/0.99      | k4_tarski(sK0(sK2),X0) != sK2 ),
% 1.98/0.99      inference(global_propositional_subsumption,
% 1.98/0.99                [status(thm)],
% 1.98/0.99                [c_2385,c_1386]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2391,plain,
% 1.98/0.99      ( k4_tarski(sK0(sK2),X0) != sK2
% 1.98/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 1.98/0.99      inference(renaming,[status(thm)],[c_2390]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_2398,plain,
% 1.98/0.99      ( r2_hidden(sK1(sK2),sK6) != iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_678,c_2391]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_896,plain,
% 1.98/0.99      ( k2_mcart_1(sK2) = sK1(sK2) ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_678,c_4]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_560,plain,
% 1.98/0.99      ( r2_hidden(k2_mcart_1(sK2),sK6) = iProver_top ),
% 1.98/0.99      inference(superposition,[status(thm)],[c_174,c_177]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(c_1015,plain,
% 1.98/0.99      ( r2_hidden(sK1(sK2),sK6) = iProver_top ),
% 1.98/0.99      inference(demodulation,[status(thm)],[c_896,c_560]) ).
% 1.98/0.99  
% 1.98/0.99  cnf(contradiction,plain,
% 1.98/0.99      ( $false ),
% 1.98/0.99      inference(minisat,[status(thm)],[c_2398,c_1015]) ).
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.98/0.99  
% 1.98/0.99  ------                               Statistics
% 1.98/0.99  
% 1.98/0.99  ------ General
% 1.98/0.99  
% 1.98/0.99  abstr_ref_over_cycles:                  0
% 1.98/0.99  abstr_ref_under_cycles:                 0
% 1.98/0.99  gc_basic_clause_elim:                   0
% 1.98/0.99  forced_gc_time:                         0
% 1.98/0.99  parsing_time:                           0.007
% 1.98/0.99  unif_index_cands_time:                  0.
% 1.98/0.99  unif_index_add_time:                    0.
% 1.98/0.99  orderings_time:                         0.
% 1.98/0.99  out_proof_time:                         0.006
% 1.98/0.99  total_time:                             0.116
% 1.98/0.99  num_of_symbols:                         44
% 1.98/0.99  num_of_terms:                           3351
% 1.98/0.99  
% 1.98/0.99  ------ Preprocessing
% 1.98/0.99  
% 1.98/0.99  num_of_splits:                          0
% 1.98/0.99  num_of_split_atoms:                     0
% 1.98/0.99  num_of_reused_defs:                     0
% 1.98/0.99  num_eq_ax_congr_red:                    10
% 1.98/0.99  num_of_sem_filtered_clauses:            1
% 1.98/0.99  num_of_subtypes:                        0
% 1.98/0.99  monotx_restored_types:                  0
% 1.98/0.99  sat_num_of_epr_types:                   0
% 1.98/0.99  sat_num_of_non_cyclic_types:            0
% 1.98/0.99  sat_guarded_non_collapsed_types:        0
% 1.98/0.99  num_pure_diseq_elim:                    0
% 1.98/0.99  simp_replaced_by:                       0
% 1.98/0.99  res_preprocessed:                       39
% 1.98/0.99  prep_upred:                             0
% 1.98/0.99  prep_unflattend:                        0
% 1.98/0.99  smt_new_axioms:                         0
% 1.98/0.99  pred_elim_cands:                        1
% 1.98/0.99  pred_elim:                              0
% 1.98/0.99  pred_elim_cl:                           0
% 1.98/0.99  pred_elim_cycles:                       1
% 1.98/0.99  merged_defs:                            0
% 1.98/0.99  merged_defs_ncl:                        0
% 1.98/0.99  bin_hyper_res:                          0
% 1.98/0.99  prep_cycles:                            3
% 1.98/0.99  pred_elim_time:                         0.
% 1.98/0.99  splitting_time:                         0.
% 1.98/0.99  sem_filter_time:                        0.
% 1.98/0.99  monotx_time:                            0.
% 1.98/0.99  subtype_inf_time:                       0.
% 1.98/0.99  
% 1.98/0.99  ------ Problem properties
% 1.98/0.99  
% 1.98/0.99  clauses:                                8
% 1.98/0.99  conjectures:                            2
% 1.98/0.99  epr:                                    0
% 1.98/0.99  horn:                                   8
% 1.98/0.99  ground:                                 1
% 1.98/0.99  unary:                                  4
% 1.98/0.99  binary:                                 3
% 1.98/0.99  lits:                                   15
% 1.98/0.99  lits_eq:                                5
% 1.98/0.99  fd_pure:                                0
% 1.98/0.99  fd_pseudo:                              0
% 1.98/0.99  fd_cond:                                0
% 1.98/0.99  fd_pseudo_cond:                         0
% 1.98/0.99  ac_symbols:                             0
% 1.98/0.99  
% 1.98/0.99  ------ Propositional Solver
% 1.98/0.99  
% 1.98/0.99  prop_solver_calls:                      23
% 1.98/0.99  prop_fast_solver_calls:                 247
% 1.98/0.99  smt_solver_calls:                       0
% 1.98/0.99  smt_fast_solver_calls:                  0
% 1.98/0.99  prop_num_of_clauses:                    1116
% 1.98/0.99  prop_preprocess_simplified:             2936
% 1.98/0.99  prop_fo_subsumed:                       3
% 1.98/0.99  prop_solver_time:                       0.
% 1.98/0.99  smt_solver_time:                        0.
% 1.98/0.99  smt_fast_solver_time:                   0.
% 1.98/0.99  prop_fast_solver_time:                  0.
% 1.98/0.99  prop_unsat_core_time:                   0.
% 1.98/0.99  
% 1.98/0.99  ------ QBF
% 1.98/0.99  
% 1.98/0.99  qbf_q_res:                              0
% 1.98/0.99  qbf_num_tautologies:                    0
% 1.98/0.99  qbf_prep_cycles:                        0
% 1.98/0.99  
% 1.98/0.99  ------ BMC1
% 1.98/0.99  
% 1.98/0.99  bmc1_current_bound:                     -1
% 1.98/0.99  bmc1_last_solved_bound:                 -1
% 1.98/0.99  bmc1_unsat_core_size:                   -1
% 1.98/0.99  bmc1_unsat_core_parents_size:           -1
% 1.98/0.99  bmc1_merge_next_fun:                    0
% 1.98/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.98/0.99  
% 1.98/0.99  ------ Instantiation
% 1.98/0.99  
% 1.98/0.99  inst_num_of_clauses:                    404
% 1.98/0.99  inst_num_in_passive:                    88
% 1.98/0.99  inst_num_in_active:                     208
% 1.98/0.99  inst_num_in_unprocessed:                108
% 1.98/0.99  inst_num_of_loops:                      210
% 1.98/0.99  inst_num_of_learning_restarts:          0
% 1.98/0.99  inst_num_moves_active_passive:          0
% 1.98/0.99  inst_lit_activity:                      0
% 1.98/0.99  inst_lit_activity_moves:                0
% 1.98/0.99  inst_num_tautologies:                   0
% 1.98/0.99  inst_num_prop_implied:                  0
% 1.98/0.99  inst_num_existing_simplified:           0
% 1.98/0.99  inst_num_eq_res_simplified:             0
% 1.98/0.99  inst_num_child_elim:                    0
% 1.98/0.99  inst_num_of_dismatching_blockings:      52
% 1.98/0.99  inst_num_of_non_proper_insts:           302
% 1.98/0.99  inst_num_of_duplicates:                 0
% 1.98/0.99  inst_inst_num_from_inst_to_res:         0
% 1.98/0.99  inst_dismatching_checking_time:         0.
% 1.98/0.99  
% 1.98/0.99  ------ Resolution
% 1.98/0.99  
% 1.98/0.99  res_num_of_clauses:                     0
% 1.98/0.99  res_num_in_passive:                     0
% 1.98/0.99  res_num_in_active:                      0
% 1.98/0.99  res_num_of_loops:                       42
% 1.98/0.99  res_forward_subset_subsumed:            18
% 1.98/0.99  res_backward_subset_subsumed:           0
% 1.98/0.99  res_forward_subsumed:                   0
% 1.98/0.99  res_backward_subsumed:                  0
% 1.98/0.99  res_forward_subsumption_resolution:     0
% 1.98/0.99  res_backward_subsumption_resolution:    0
% 1.98/0.99  res_clause_to_clause_subsumption:       59
% 1.98/0.99  res_orphan_elimination:                 0
% 1.98/0.99  res_tautology_del:                      48
% 1.98/0.99  res_num_eq_res_simplified:              0
% 1.98/0.99  res_num_sel_changes:                    0
% 1.98/0.99  res_moves_from_active_to_pass:          0
% 1.98/0.99  
% 1.98/0.99  ------ Superposition
% 1.98/0.99  
% 1.98/0.99  sup_time_total:                         0.
% 1.98/0.99  sup_time_generating:                    0.
% 1.98/0.99  sup_time_sim_full:                      0.
% 1.98/0.99  sup_time_sim_immed:                     0.
% 1.98/0.99  
% 1.98/0.99  sup_num_of_clauses:                     38
% 1.98/0.99  sup_num_in_active:                      35
% 1.98/0.99  sup_num_in_passive:                     3
% 1.98/0.99  sup_num_of_loops:                       41
% 1.98/0.99  sup_fw_superposition:                   14
% 1.98/0.99  sup_bw_superposition:                   43
% 1.98/0.99  sup_immediate_simplified:               24
% 1.98/0.99  sup_given_eliminated:                   1
% 1.98/0.99  comparisons_done:                       0
% 1.98/0.99  comparisons_avoided:                    0
% 1.98/0.99  
% 1.98/0.99  ------ Simplifications
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  sim_fw_subset_subsumed:                 0
% 1.98/0.99  sim_bw_subset_subsumed:                 0
% 1.98/0.99  sim_fw_subsumed:                        17
% 1.98/0.99  sim_bw_subsumed:                        0
% 1.98/0.99  sim_fw_subsumption_res:                 0
% 1.98/0.99  sim_bw_subsumption_res:                 0
% 1.98/0.99  sim_tautology_del:                      0
% 1.98/0.99  sim_eq_tautology_del:                   3
% 1.98/0.99  sim_eq_res_simp:                        0
% 1.98/0.99  sim_fw_demodulated:                     10
% 1.98/0.99  sim_bw_demodulated:                     8
% 1.98/0.99  sim_light_normalised:                   20
% 1.98/0.99  sim_joinable_taut:                      0
% 1.98/0.99  sim_joinable_simp:                      0
% 1.98/0.99  sim_ac_normalised:                      0
% 1.98/0.99  sim_smt_subsumption:                    0
% 1.98/0.99  
%------------------------------------------------------------------------------
