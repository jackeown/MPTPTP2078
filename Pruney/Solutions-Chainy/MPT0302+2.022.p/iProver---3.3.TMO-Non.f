%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:06 EST 2020

% Result     : Timeout 58.97s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  133 ( 241 expanded)
%              Number of clauses        :   82 ( 101 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  327 ( 683 expanded)
%              Number of equality atoms :  183 ( 335 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK6 != sK7
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( sK6 != sK7
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f25,f40])).

fof(f68,plain,(
    sK6 != sK7 ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f38])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f28])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f46,f54])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_301,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_89219,plain,
    ( X0 != X1
    | k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)) != X1
    | k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)) = X0 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_199666,plain,
    ( X0 != k5_xboole_0(X1,X2)
    | k5_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X3,X4)) = X0
    | k5_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X3,X4)) != k5_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_89219])).

cnf(c_199667,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_199666])).

cnf(c_300,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1717,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_301,c_300])).

cnf(c_2,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13066,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(resolution,[status(thm)],[c_1717,c_2])).

cnf(c_22,negated_conjecture,
    ( sK6 != sK7 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_145824,plain,
    ( r2_xboole_0(sK6,sK7)
    | ~ r1_tarski(sK6,sK7) ),
    inference(resolution,[status(thm)],[c_13066,c_22])).

cnf(c_145825,plain,
    ( r2_xboole_0(sK6,sK7) = iProver_top
    | r1_tarski(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145824])).

cnf(c_304,plain,
    ( X0 != X1
    | X2 != X3
    | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_89221,plain,
    ( k2_xboole_0(X0,X1) != X2
    | k5_xboole_0(X0,X1) != X3
    | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k5_xboole_0(X3,X2) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_89226,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_89221])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_634,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_629,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_621,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_25,negated_conjecture,
    ( k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_620,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1779,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_620])).

cnf(c_3112,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_1779])).

cnf(c_26485,plain,
    ( r2_xboole_0(X0,sK7) != iProver_top
    | r2_hidden(X1,sK6) != iProver_top
    | r2_hidden(sK2(X0,sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_3112])).

cnf(c_27301,plain,
    ( r2_xboole_0(X0,sK7) != iProver_top
    | r2_hidden(sK2(X0,sK7),sK6) = iProver_top
    | r1_tarski(sK6,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_26485])).

cnf(c_5,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_630,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK2(X0,X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_31904,plain,
    ( r2_xboole_0(sK6,sK7) != iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_27301,c_630])).

cnf(c_31930,plain,
    ( r2_xboole_0(sK6,sK7) != iProver_top
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_31904])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_619,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_883,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_619])).

cnf(c_3111,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK7) = iProver_top
    | r2_hidden(X1,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_621,c_883])).

cnf(c_11036,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(sK7,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_3111])).

cnf(c_13037,plain,
    ( r2_hidden(sK0(sK6,X0),sK7) = iProver_top
    | r1_tarski(sK7,X1) = iProver_top
    | r1_tarski(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_11036])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_635,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_26530,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | r1_tarski(sK6,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_13037,c_635])).

cnf(c_26546,plain,
    ( r1_tarski(sK7,k1_xboole_0) = iProver_top
    | r1_tarski(sK6,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_26530])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_13070,plain,
    ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1717,c_8])).

cnf(c_13071,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13070])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_12847,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12852,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12847])).

cnf(c_12854,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12852])).

cnf(c_302,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1028,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0)
    | X0 != sK2(sK6,k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_1367,plain,
    ( ~ r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),X0)
    | X0 != k1_xboole_0
    | k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0) != sK2(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_12846,plain,
    ( ~ r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))
    | k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0) != sK2(sK6,k1_xboole_0)
    | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_12848,plain,
    ( k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0) != sK2(sK6,k1_xboole_0)
    | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
    | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12846])).

cnf(c_12850,plain,
    ( k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0) != sK2(sK6,k1_xboole_0)
    | k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
    | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12848])).

cnf(c_12669,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12674,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12669])).

cnf(c_12676,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12674])).

cnf(c_1008,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0)
    | X0 != sK2(sK7,k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_1329,plain,
    ( ~ r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),X0)
    | X0 != k1_xboole_0
    | k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0) != sK2(sK7,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_12668,plain,
    ( ~ r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))
    | k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0) != sK2(sK7,k1_xboole_0)
    | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1329])).

cnf(c_12670,plain,
    ( k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0) != sK2(sK7,k1_xboole_0)
    | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k1_xboole_0
    | r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0) != iProver_top
    | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12668])).

cnf(c_12672,plain,
    ( k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0) != sK2(sK7,k1_xboole_0)
    | k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0) != iProver_top
    | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12670])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1368,plain,
    ( k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0) = sK2(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1330,plain,
    ( k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0) = sK2(sK7,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_829,plain,
    ( ~ r2_xboole_0(sK6,k1_xboole_0)
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_833,plain,
    ( r2_xboole_0(sK6,k1_xboole_0) != iProver_top
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_823,plain,
    ( ~ r2_xboole_0(sK7,k1_xboole_0)
    | r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_827,plain,
    ( r2_xboole_0(sK7,k1_xboole_0) != iProver_top
    | r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_823])).

cnf(c_792,plain,
    ( r2_xboole_0(sK6,k1_xboole_0)
    | ~ r1_tarski(sK6,k1_xboole_0)
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_793,plain,
    ( k1_xboole_0 = sK6
    | r2_xboole_0(sK6,k1_xboole_0) = iProver_top
    | r1_tarski(sK6,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_789,plain,
    ( r2_xboole_0(sK7,k1_xboole_0)
    | ~ r1_tarski(sK7,k1_xboole_0)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_790,plain,
    ( k1_xboole_0 = sK7
    | r2_xboole_0(sK7,k1_xboole_0) = iProver_top
    | r1_tarski(sK7,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_50,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_47,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_49,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_45,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_199667,c_145825,c_89226,c_31930,c_26546,c_13071,c_12854,c_12850,c_12676,c_12672,c_1368,c_1330,c_833,c_827,c_793,c_790,c_50,c_49,c_45,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 58.97/8.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.97/8.01  
% 58.97/8.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 58.97/8.01  
% 58.97/8.01  ------  iProver source info
% 58.97/8.01  
% 58.97/8.01  git: date: 2020-06-30 10:37:57 +0100
% 58.97/8.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 58.97/8.01  git: non_committed_changes: false
% 58.97/8.01  git: last_make_outside_of_git: false
% 58.97/8.01  
% 58.97/8.01  ------ 
% 58.97/8.01  ------ Parsing...
% 58.97/8.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 58.97/8.01  
% 58.97/8.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 58.97/8.01  
% 58.97/8.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 58.97/8.01  
% 58.97/8.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 58.97/8.01  ------ Proving...
% 58.97/8.01  ------ Problem Properties 
% 58.97/8.01  
% 58.97/8.01  
% 58.97/8.01  clauses                                 26
% 58.97/8.01  conjectures                             4
% 58.97/8.01  EPR                                     5
% 58.97/8.01  Horn                                    21
% 58.97/8.01  unary                                   10
% 58.97/8.01  binary                                  10
% 58.97/8.01  lits                                    49
% 58.97/8.01  lits eq                                 13
% 58.97/8.01  fd_pure                                 0
% 58.97/8.01  fd_pseudo                               0
% 58.97/8.01  fd_cond                                 0
% 58.97/8.01  fd_pseudo_cond                          4
% 58.97/8.01  AC symbols                              0
% 58.97/8.01  
% 58.97/8.01  ------ Input Options Time Limit: Unbounded
% 58.97/8.01  
% 58.97/8.01  
% 58.97/8.01  ------ 
% 58.97/8.01  Current options:
% 58.97/8.01  ------ 
% 58.97/8.01  
% 58.97/8.01  
% 58.97/8.01  
% 58.97/8.01  
% 58.97/8.01  ------ Proving...
% 58.97/8.01  
% 58.97/8.01  
% 58.97/8.01  % SZS status Theorem for theBenchmark.p
% 58.97/8.01  
% 58.97/8.01  % SZS output start CNFRefutation for theBenchmark.p
% 58.97/8.01  
% 58.97/8.01  fof(f2,axiom,(
% 58.97/8.01    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 58.97/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.97/8.01  
% 58.97/8.01  fof(f17,plain,(
% 58.97/8.01    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 58.97/8.01    inference(unused_predicate_definition_removal,[],[f2])).
% 58.97/8.01  
% 58.97/8.01  fof(f20,plain,(
% 58.97/8.01    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 58.97/8.01    inference(ennf_transformation,[],[f17])).
% 58.97/8.01  
% 58.97/8.01  fof(f21,plain,(
% 58.97/8.01    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 58.97/8.01    inference(flattening,[],[f20])).
% 58.97/8.01  
% 58.97/8.01  fof(f44,plain,(
% 58.97/8.01    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 58.97/8.01    inference(cnf_transformation,[],[f21])).
% 58.97/8.01  
% 58.97/8.01  fof(f14,conjecture,(
% 58.97/8.01    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 58.97/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.97/8.01  
% 58.97/8.01  fof(f15,negated_conjecture,(
% 58.97/8.01    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 58.97/8.01    inference(negated_conjecture,[],[f14])).
% 58.97/8.01  
% 58.97/8.01  fof(f24,plain,(
% 58.97/8.01    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 58.97/8.01    inference(ennf_transformation,[],[f15])).
% 58.97/8.01  
% 58.97/8.01  fof(f25,plain,(
% 58.97/8.01    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 58.97/8.01    inference(flattening,[],[f24])).
% 58.97/8.01  
% 58.97/8.01  fof(f40,plain,(
% 58.97/8.01    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK6 != sK7 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6))),
% 58.97/8.01    introduced(choice_axiom,[])).
% 58.97/8.01  
% 58.97/8.01  fof(f41,plain,(
% 58.97/8.01    sK6 != sK7 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6)),
% 58.97/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f25,f40])).
% 58.97/8.01  
% 58.97/8.01  fof(f68,plain,(
% 58.97/8.01    sK6 != sK7),
% 58.97/8.01    inference(cnf_transformation,[],[f41])).
% 58.97/8.01  
% 58.97/8.01  fof(f1,axiom,(
% 58.97/8.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 58.97/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.97/8.01  
% 58.97/8.01  fof(f18,plain,(
% 58.97/8.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 58.97/8.01    inference(unused_predicate_definition_removal,[],[f1])).
% 58.97/8.01  
% 58.97/8.01  fof(f19,plain,(
% 58.97/8.01    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 58.97/8.01    inference(ennf_transformation,[],[f18])).
% 58.97/8.01  
% 58.97/8.01  fof(f26,plain,(
% 58.97/8.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 58.97/8.01    introduced(choice_axiom,[])).
% 58.97/8.01  
% 58.97/8.01  fof(f27,plain,(
% 58.97/8.01    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 58.97/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f26])).
% 58.97/8.01  
% 58.97/8.01  fof(f42,plain,(
% 58.97/8.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 58.97/8.01    inference(cnf_transformation,[],[f27])).
% 58.97/8.01  
% 58.97/8.01  fof(f4,axiom,(
% 58.97/8.01    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 58.97/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.97/8.01  
% 58.97/8.01  fof(f23,plain,(
% 58.97/8.01    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 58.97/8.01    inference(ennf_transformation,[],[f4])).
% 58.97/8.01  
% 58.97/8.01  fof(f30,plain,(
% 58.97/8.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1)))),
% 58.97/8.01    introduced(choice_axiom,[])).
% 58.97/8.01  
% 58.97/8.01  fof(f31,plain,(
% 58.97/8.01    ! [X0,X1] : ((~r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 58.97/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f30])).
% 58.97/8.01  
% 58.97/8.01  fof(f47,plain,(
% 58.97/8.01    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 58.97/8.01    inference(cnf_transformation,[],[f31])).
% 58.97/8.01  
% 58.97/8.01  fof(f12,axiom,(
% 58.97/8.01    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 58.97/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.97/8.01  
% 58.97/8.01  fof(f38,plain,(
% 58.97/8.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 58.97/8.01    inference(nnf_transformation,[],[f12])).
% 58.97/8.01  
% 58.97/8.01  fof(f39,plain,(
% 58.97/8.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 58.97/8.01    inference(flattening,[],[f38])).
% 58.97/8.01  
% 58.97/8.01  fof(f63,plain,(
% 58.97/8.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 58.97/8.01    inference(cnf_transformation,[],[f39])).
% 58.97/8.01  
% 58.97/8.01  fof(f65,plain,(
% 58.97/8.01    k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6)),
% 58.97/8.01    inference(cnf_transformation,[],[f41])).
% 58.97/8.01  
% 58.97/8.01  fof(f62,plain,(
% 58.97/8.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 58.97/8.01    inference(cnf_transformation,[],[f39])).
% 58.97/8.01  
% 58.97/8.01  fof(f48,plain,(
% 58.97/8.01    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 58.97/8.01    inference(cnf_transformation,[],[f31])).
% 58.97/8.01  
% 58.97/8.01  fof(f61,plain,(
% 58.97/8.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 58.97/8.01    inference(cnf_transformation,[],[f39])).
% 58.97/8.01  
% 58.97/8.01  fof(f43,plain,(
% 58.97/8.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 58.97/8.01    inference(cnf_transformation,[],[f27])).
% 58.97/8.01  
% 58.97/8.01  fof(f6,axiom,(
% 58.97/8.01    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 58.97/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.97/8.01  
% 58.97/8.01  fof(f50,plain,(
% 58.97/8.01    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 58.97/8.01    inference(cnf_transformation,[],[f6])).
% 58.97/8.01  
% 58.97/8.01  fof(f3,axiom,(
% 58.97/8.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 58.97/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.97/8.01  
% 58.97/8.01  fof(f16,plain,(
% 58.97/8.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 58.97/8.01    inference(rectify,[],[f3])).
% 58.97/8.01  
% 58.97/8.01  fof(f22,plain,(
% 58.97/8.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 58.97/8.01    inference(ennf_transformation,[],[f16])).
% 58.97/8.01  
% 58.97/8.01  fof(f28,plain,(
% 58.97/8.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 58.97/8.01    introduced(choice_axiom,[])).
% 58.97/8.01  
% 58.97/8.01  fof(f29,plain,(
% 58.97/8.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 58.97/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f28])).
% 58.97/8.01  
% 58.97/8.01  fof(f46,plain,(
% 58.97/8.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 58.97/8.01    inference(cnf_transformation,[],[f29])).
% 58.97/8.01  
% 58.97/8.01  fof(f10,axiom,(
% 58.97/8.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 58.97/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.97/8.01  
% 58.97/8.01  fof(f54,plain,(
% 58.97/8.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 58.97/8.01    inference(cnf_transformation,[],[f10])).
% 58.97/8.01  
% 58.97/8.01  fof(f69,plain,(
% 58.97/8.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 58.97/8.01    inference(definition_unfolding,[],[f46,f54])).
% 58.97/8.01  
% 58.97/8.01  fof(f5,axiom,(
% 58.97/8.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 58.97/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.97/8.01  
% 58.97/8.01  fof(f49,plain,(
% 58.97/8.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 58.97/8.01    inference(cnf_transformation,[],[f5])).
% 58.97/8.01  
% 58.97/8.01  fof(f7,axiom,(
% 58.97/8.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 58.97/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.97/8.01  
% 58.97/8.01  fof(f51,plain,(
% 58.97/8.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 58.97/8.01    inference(cnf_transformation,[],[f7])).
% 58.97/8.01  
% 58.97/8.01  fof(f9,axiom,(
% 58.97/8.01    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 58.97/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 58.97/8.01  
% 58.97/8.01  fof(f53,plain,(
% 58.97/8.01    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 58.97/8.01    inference(cnf_transformation,[],[f9])).
% 58.97/8.01  
% 58.97/8.01  fof(f67,plain,(
% 58.97/8.01    k1_xboole_0 != sK7),
% 58.97/8.01    inference(cnf_transformation,[],[f41])).
% 58.97/8.01  
% 58.97/8.01  fof(f66,plain,(
% 58.97/8.01    k1_xboole_0 != sK6),
% 58.97/8.01    inference(cnf_transformation,[],[f41])).
% 58.97/8.01  
% 58.97/8.01  cnf(c_301,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_89219,plain,
% 58.97/8.01      ( X0 != X1
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)) != X1
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)) = X0 ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_301]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_199666,plain,
% 58.97/8.01      ( X0 != k5_xboole_0(X1,X2)
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X3,X4)) = X0
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(X3,X4),k2_xboole_0(X3,X4)) != k5_xboole_0(X1,X2) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_89219]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_199667,plain,
% 58.97/8.01      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) != k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
% 58.97/8.01      | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_199666]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_300,plain,( X0 = X0 ),theory(equality) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_1717,plain,
% 58.97/8.01      ( X0 != X1 | X1 = X0 ),
% 58.97/8.01      inference(resolution,[status(thm)],[c_301,c_300]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_2,plain,
% 58.97/8.01      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 58.97/8.01      inference(cnf_transformation,[],[f44]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_13066,plain,
% 58.97/8.01      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 58.97/8.01      inference(resolution,[status(thm)],[c_1717,c_2]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_22,negated_conjecture,
% 58.97/8.01      ( sK6 != sK7 ),
% 58.97/8.01      inference(cnf_transformation,[],[f68]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_145824,plain,
% 58.97/8.01      ( r2_xboole_0(sK6,sK7) | ~ r1_tarski(sK6,sK7) ),
% 58.97/8.01      inference(resolution,[status(thm)],[c_13066,c_22]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_145825,plain,
% 58.97/8.01      ( r2_xboole_0(sK6,sK7) = iProver_top
% 58.97/8.01      | r1_tarski(sK6,sK7) != iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_145824]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_304,plain,
% 58.97/8.01      ( X0 != X1 | X2 != X3 | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
% 58.97/8.01      theory(equality) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_89221,plain,
% 58.97/8.01      ( k2_xboole_0(X0,X1) != X2
% 58.97/8.01      | k5_xboole_0(X0,X1) != X3
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k5_xboole_0(X3,X2) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_304]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_89226,plain,
% 58.97/8.01      ( k2_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
% 58.97/8.01      | k5_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_89221]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_1,plain,
% 58.97/8.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 58.97/8.01      inference(cnf_transformation,[],[f42]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_634,plain,
% 58.97/8.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 58.97/8.01      | r1_tarski(X0,X1) = iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_6,plain,
% 58.97/8.01      ( ~ r2_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1) ),
% 58.97/8.01      inference(cnf_transformation,[],[f47]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_629,plain,
% 58.97/8.01      ( r2_xboole_0(X0,X1) != iProver_top
% 58.97/8.01      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_18,plain,
% 58.97/8.01      ( ~ r2_hidden(X0,X1)
% 58.97/8.01      | ~ r2_hidden(X2,X3)
% 58.97/8.01      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 58.97/8.01      inference(cnf_transformation,[],[f63]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_621,plain,
% 58.97/8.01      ( r2_hidden(X0,X1) != iProver_top
% 58.97/8.01      | r2_hidden(X2,X3) != iProver_top
% 58.97/8.01      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_25,negated_conjecture,
% 58.97/8.01      ( k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK7,sK6) ),
% 58.97/8.01      inference(cnf_transformation,[],[f65]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_19,plain,
% 58.97/8.01      ( r2_hidden(X0,X1)
% 58.97/8.01      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 58.97/8.01      inference(cnf_transformation,[],[f62]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_620,plain,
% 58.97/8.01      ( r2_hidden(X0,X1) = iProver_top
% 58.97/8.01      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_1779,plain,
% 58.97/8.01      ( r2_hidden(X0,sK6) = iProver_top
% 58.97/8.01      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
% 58.97/8.01      inference(superposition,[status(thm)],[c_25,c_620]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_3112,plain,
% 58.97/8.01      ( r2_hidden(X0,sK7) != iProver_top
% 58.97/8.01      | r2_hidden(X1,sK6) != iProver_top
% 58.97/8.01      | r2_hidden(X0,sK6) = iProver_top ),
% 58.97/8.01      inference(superposition,[status(thm)],[c_621,c_1779]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_26485,plain,
% 58.97/8.01      ( r2_xboole_0(X0,sK7) != iProver_top
% 58.97/8.01      | r2_hidden(X1,sK6) != iProver_top
% 58.97/8.01      | r2_hidden(sK2(X0,sK7),sK6) = iProver_top ),
% 58.97/8.01      inference(superposition,[status(thm)],[c_629,c_3112]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_27301,plain,
% 58.97/8.01      ( r2_xboole_0(X0,sK7) != iProver_top
% 58.97/8.01      | r2_hidden(sK2(X0,sK7),sK6) = iProver_top
% 58.97/8.01      | r1_tarski(sK6,X1) = iProver_top ),
% 58.97/8.01      inference(superposition,[status(thm)],[c_634,c_26485]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_5,plain,
% 58.97/8.01      ( ~ r2_xboole_0(X0,X1) | ~ r2_hidden(sK2(X0,X1),X0) ),
% 58.97/8.01      inference(cnf_transformation,[],[f48]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_630,plain,
% 58.97/8.01      ( r2_xboole_0(X0,X1) != iProver_top
% 58.97/8.01      | r2_hidden(sK2(X0,X1),X0) != iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_31904,plain,
% 58.97/8.01      ( r2_xboole_0(sK6,sK7) != iProver_top
% 58.97/8.01      | r1_tarski(sK6,X0) = iProver_top ),
% 58.97/8.01      inference(superposition,[status(thm)],[c_27301,c_630]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_31930,plain,
% 58.97/8.01      ( r2_xboole_0(sK6,sK7) != iProver_top
% 58.97/8.01      | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_31904]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_20,plain,
% 58.97/8.01      ( r2_hidden(X0,X1)
% 58.97/8.01      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 58.97/8.01      inference(cnf_transformation,[],[f61]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_619,plain,
% 58.97/8.01      ( r2_hidden(X0,X1) = iProver_top
% 58.97/8.01      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_883,plain,
% 58.97/8.01      ( r2_hidden(X0,sK7) = iProver_top
% 58.97/8.01      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
% 58.97/8.01      inference(superposition,[status(thm)],[c_25,c_619]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_3111,plain,
% 58.97/8.01      ( r2_hidden(X0,sK7) != iProver_top
% 58.97/8.01      | r2_hidden(X1,sK7) = iProver_top
% 58.97/8.01      | r2_hidden(X1,sK6) != iProver_top ),
% 58.97/8.01      inference(superposition,[status(thm)],[c_621,c_883]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_11036,plain,
% 58.97/8.01      ( r2_hidden(X0,sK7) = iProver_top
% 58.97/8.01      | r2_hidden(X0,sK6) != iProver_top
% 58.97/8.01      | r1_tarski(sK7,X1) = iProver_top ),
% 58.97/8.01      inference(superposition,[status(thm)],[c_634,c_3111]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_13037,plain,
% 58.97/8.01      ( r2_hidden(sK0(sK6,X0),sK7) = iProver_top
% 58.97/8.01      | r1_tarski(sK7,X1) = iProver_top
% 58.97/8.01      | r1_tarski(sK6,X0) = iProver_top ),
% 58.97/8.01      inference(superposition,[status(thm)],[c_634,c_11036]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_0,plain,
% 58.97/8.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 58.97/8.01      inference(cnf_transformation,[],[f43]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_635,plain,
% 58.97/8.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 58.97/8.01      | r1_tarski(X0,X1) = iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_26530,plain,
% 58.97/8.01      ( r1_tarski(sK7,X0) = iProver_top
% 58.97/8.01      | r1_tarski(sK6,sK7) = iProver_top ),
% 58.97/8.01      inference(superposition,[status(thm)],[c_13037,c_635]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_26546,plain,
% 58.97/8.01      ( r1_tarski(sK7,k1_xboole_0) = iProver_top
% 58.97/8.01      | r1_tarski(sK6,sK7) = iProver_top ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_26530]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_8,plain,
% 58.97/8.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 58.97/8.01      inference(cnf_transformation,[],[f50]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_13070,plain,
% 58.97/8.01      ( X0 = k5_xboole_0(X0,k1_xboole_0) ),
% 58.97/8.01      inference(resolution,[status(thm)],[c_1717,c_8]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_13071,plain,
% 58.97/8.01      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_13070]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_3,plain,
% 58.97/8.01      ( ~ r1_xboole_0(X0,X1)
% 58.97/8.01      | ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
% 58.97/8.01      inference(cnf_transformation,[],[f69]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12847,plain,
% 58.97/8.01      ( ~ r1_xboole_0(X0,X1)
% 58.97/8.01      | ~ r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_3]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12852,plain,
% 58.97/8.01      ( r1_xboole_0(X0,X1) != iProver_top
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_12847]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12854,plain,
% 58.97/8.01      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_12852]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_302,plain,
% 58.97/8.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 58.97/8.01      theory(equality) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_1028,plain,
% 58.97/8.01      ( r2_hidden(X0,X1)
% 58.97/8.01      | ~ r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0)
% 58.97/8.01      | X0 != sK2(sK6,k1_xboole_0)
% 58.97/8.01      | X1 != k1_xboole_0 ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_302]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_1367,plain,
% 58.97/8.01      ( ~ r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0)
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),X0)
% 58.97/8.01      | X0 != k1_xboole_0
% 58.97/8.01      | k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0) != sK2(sK6,k1_xboole_0) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_1028]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12846,plain,
% 58.97/8.01      ( ~ r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0)
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))
% 58.97/8.01      | k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0) != sK2(sK6,k1_xboole_0)
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k1_xboole_0 ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_1367]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12848,plain,
% 58.97/8.01      ( k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0) != sK2(sK6,k1_xboole_0)
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k1_xboole_0
% 58.97/8.01      | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_12846]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12850,plain,
% 58.97/8.01      ( k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0) != sK2(sK6,k1_xboole_0)
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 58.97/8.01      | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_12848]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12669,plain,
% 58.97/8.01      ( ~ r1_xboole_0(X0,X1)
% 58.97/8.01      | ~ r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_3]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12674,plain,
% 58.97/8.01      ( r1_xboole_0(X0,X1) != iProver_top
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_12669]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12676,plain,
% 58.97/8.01      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_12674]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_1008,plain,
% 58.97/8.01      ( r2_hidden(X0,X1)
% 58.97/8.01      | ~ r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0)
% 58.97/8.01      | X0 != sK2(sK7,k1_xboole_0)
% 58.97/8.01      | X1 != k1_xboole_0 ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_302]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_1329,plain,
% 58.97/8.01      ( ~ r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0)
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),X0)
% 58.97/8.01      | X0 != k1_xboole_0
% 58.97/8.01      | k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0) != sK2(sK7,k1_xboole_0) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_1008]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12668,plain,
% 58.97/8.01      ( ~ r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0)
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))
% 58.97/8.01      | k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0) != sK2(sK7,k1_xboole_0)
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k1_xboole_0 ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_1329]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12670,plain,
% 58.97/8.01      ( k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0) != sK2(sK7,k1_xboole_0)
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) != k1_xboole_0
% 58.97/8.01      | r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0) != iProver_top
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_12668]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_12672,plain,
% 58.97/8.01      ( k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0) != sK2(sK7,k1_xboole_0)
% 58.97/8.01      | k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 58.97/8.01      | r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0) != iProver_top
% 58.97/8.01      | r2_hidden(k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k2_xboole_0(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_12670]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_7,plain,
% 58.97/8.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 58.97/8.01      inference(cnf_transformation,[],[f49]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_1368,plain,
% 58.97/8.01      ( k2_xboole_0(sK2(sK6,k1_xboole_0),k1_xboole_0) = sK2(sK6,k1_xboole_0) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_7]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_1330,plain,
% 58.97/8.01      ( k2_xboole_0(sK2(sK7,k1_xboole_0),k1_xboole_0) = sK2(sK7,k1_xboole_0) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_7]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_829,plain,
% 58.97/8.01      ( ~ r2_xboole_0(sK6,k1_xboole_0)
% 58.97/8.01      | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_6]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_833,plain,
% 58.97/8.01      ( r2_xboole_0(sK6,k1_xboole_0) != iProver_top
% 58.97/8.01      | r2_hidden(sK2(sK6,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_823,plain,
% 58.97/8.01      ( ~ r2_xboole_0(sK7,k1_xboole_0)
% 58.97/8.01      | r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0) ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_6]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_827,plain,
% 58.97/8.01      ( r2_xboole_0(sK7,k1_xboole_0) != iProver_top
% 58.97/8.01      | r2_hidden(sK2(sK7,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_823]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_792,plain,
% 58.97/8.01      ( r2_xboole_0(sK6,k1_xboole_0)
% 58.97/8.01      | ~ r1_tarski(sK6,k1_xboole_0)
% 58.97/8.01      | k1_xboole_0 = sK6 ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_2]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_793,plain,
% 58.97/8.01      ( k1_xboole_0 = sK6
% 58.97/8.01      | r2_xboole_0(sK6,k1_xboole_0) = iProver_top
% 58.97/8.01      | r1_tarski(sK6,k1_xboole_0) != iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_789,plain,
% 58.97/8.01      ( r2_xboole_0(sK7,k1_xboole_0)
% 58.97/8.01      | ~ r1_tarski(sK7,k1_xboole_0)
% 58.97/8.01      | k1_xboole_0 = sK7 ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_2]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_790,plain,
% 58.97/8.01      ( k1_xboole_0 = sK7
% 58.97/8.01      | r2_xboole_0(sK7,k1_xboole_0) = iProver_top
% 58.97/8.01      | r1_tarski(sK7,k1_xboole_0) != iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_50,plain,
% 58.97/8.01      ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_7]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_9,plain,
% 58.97/8.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 58.97/8.01      inference(cnf_transformation,[],[f51]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_47,plain,
% 58.97/8.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 58.97/8.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_49,plain,
% 58.97/8.01      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_47]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_11,plain,
% 58.97/8.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 58.97/8.01      inference(cnf_transformation,[],[f53]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_45,plain,
% 58.97/8.01      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 58.97/8.01      inference(instantiation,[status(thm)],[c_11]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_23,negated_conjecture,
% 58.97/8.01      ( k1_xboole_0 != sK7 ),
% 58.97/8.01      inference(cnf_transformation,[],[f67]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(c_24,negated_conjecture,
% 58.97/8.01      ( k1_xboole_0 != sK6 ),
% 58.97/8.01      inference(cnf_transformation,[],[f66]) ).
% 58.97/8.01  
% 58.97/8.01  cnf(contradiction,plain,
% 58.97/8.01      ( $false ),
% 58.97/8.01      inference(minisat,
% 58.97/8.01                [status(thm)],
% 58.97/8.01                [c_199667,c_145825,c_89226,c_31930,c_26546,c_13071,
% 58.97/8.01                 c_12854,c_12850,c_12676,c_12672,c_1368,c_1330,c_833,
% 58.97/8.01                 c_827,c_793,c_790,c_50,c_49,c_45,c_23,c_24]) ).
% 58.97/8.01  
% 58.97/8.01  
% 58.97/8.01  % SZS output end CNFRefutation for theBenchmark.p
% 58.97/8.01  
% 58.97/8.01  ------                               Statistics
% 58.97/8.01  
% 58.97/8.01  ------ Selected
% 58.97/8.01  
% 58.97/8.01  total_time:                             7.404
% 58.97/8.01  
%------------------------------------------------------------------------------
