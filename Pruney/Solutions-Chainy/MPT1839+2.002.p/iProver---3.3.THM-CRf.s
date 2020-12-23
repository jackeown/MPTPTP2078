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
% DateTime   : Thu Dec  3 12:24:41 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 151 expanded)
%              Number of clauses        :   44 (  56 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  234 ( 471 expanded)
%              Number of equality atoms :   70 (  94 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
     => ( ~ r1_tarski(X0,sK5)
        & ~ v1_xboole_0(k3_xboole_0(X0,sK5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK4,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK4,X1)) )
      & v1_zfmisc_1(sK4)
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ r1_tarski(sK4,sK5)
    & ~ v1_xboole_0(k3_xboole_0(sK4,sK5))
    & v1_zfmisc_1(sK4)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f44,f43])).

fof(f72,plain,(
    v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK4,sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,(
    ~ v1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) ),
    inference(definition_unfolding,[],[f73,f64])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ~ r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1219,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,negated_conjecture,
    ( v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_282,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_283,plain,
    ( ~ r1_tarski(X0,sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 = X0 ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_285,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK4)
    | sK4 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_283,c_24])).

cnf(c_286,plain,
    ( ~ r1_tarski(X0,sK4)
    | v1_xboole_0(X0)
    | sK4 = X0 ),
    inference(renaming,[status(thm)],[c_285])).

cnf(c_1215,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_1785,plain,
    ( k4_xboole_0(sK4,X0) = sK4
    | v1_xboole_0(k4_xboole_0(sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1215])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1231,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1233,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2561,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1231,c_1233])).

cnf(c_15,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1220,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1224,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2351,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_1224])).

cnf(c_2789,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2561,c_2351])).

cnf(c_2855,plain,
    ( k4_xboole_0(sK4,X0) = sK4
    | k4_xboole_0(sK4,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1785,c_2789])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1217,plain,
    ( v1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1951,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = sK4 ),
    inference(superposition,[status(thm)],[c_1785,c_1217])).

cnf(c_2866,plain,
    ( k4_xboole_0(sK4,sK5) = k1_xboole_0
    | k4_xboole_0(sK4,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_2855,c_1951])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1223,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1222,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2195,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1223,c_1222])).

cnf(c_2874,plain,
    ( k4_xboole_0(sK4,sK5) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2866,c_2195])).

cnf(c_1590,plain,
    ( r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_761,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1392,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK5)
    | sK5 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_1435,plain,
    ( ~ r1_tarski(X0,sK5)
    | r1_tarski(sK4,sK5)
    | sK5 != sK5
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_1589,plain,
    ( r1_tarski(sK4,sK5)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | sK5 != sK5
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_757,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1436,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1364,plain,
    ( r1_tarski(sK4,sK5)
    | k4_xboole_0(sK4,sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2874,c_1590,c_1589,c_1436,c_1364,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.11/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.02  
% 2.11/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.11/1.02  
% 2.11/1.02  ------  iProver source info
% 2.11/1.02  
% 2.11/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.11/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.11/1.02  git: non_committed_changes: false
% 2.11/1.02  git: last_make_outside_of_git: false
% 2.11/1.02  
% 2.11/1.02  ------ 
% 2.11/1.02  
% 2.11/1.02  ------ Input Options
% 2.11/1.02  
% 2.11/1.02  --out_options                           all
% 2.11/1.02  --tptp_safe_out                         true
% 2.11/1.02  --problem_path                          ""
% 2.11/1.02  --include_path                          ""
% 2.11/1.02  --clausifier                            res/vclausify_rel
% 2.11/1.02  --clausifier_options                    --mode clausify
% 2.11/1.02  --stdin                                 false
% 2.11/1.02  --stats_out                             all
% 2.11/1.02  
% 2.11/1.02  ------ General Options
% 2.11/1.02  
% 2.11/1.02  --fof                                   false
% 2.11/1.02  --time_out_real                         305.
% 2.11/1.02  --time_out_virtual                      -1.
% 2.11/1.02  --symbol_type_check                     false
% 2.11/1.02  --clausify_out                          false
% 2.11/1.02  --sig_cnt_out                           false
% 2.11/1.02  --trig_cnt_out                          false
% 2.11/1.02  --trig_cnt_out_tolerance                1.
% 2.11/1.02  --trig_cnt_out_sk_spl                   false
% 2.11/1.02  --abstr_cl_out                          false
% 2.11/1.02  
% 2.11/1.02  ------ Global Options
% 2.11/1.02  
% 2.11/1.02  --schedule                              default
% 2.11/1.02  --add_important_lit                     false
% 2.11/1.02  --prop_solver_per_cl                    1000
% 2.11/1.02  --min_unsat_core                        false
% 2.11/1.02  --soft_assumptions                      false
% 2.11/1.02  --soft_lemma_size                       3
% 2.11/1.02  --prop_impl_unit_size                   0
% 2.11/1.02  --prop_impl_unit                        []
% 2.11/1.02  --share_sel_clauses                     true
% 2.11/1.02  --reset_solvers                         false
% 2.11/1.02  --bc_imp_inh                            [conj_cone]
% 2.11/1.02  --conj_cone_tolerance                   3.
% 2.11/1.02  --extra_neg_conj                        none
% 2.11/1.02  --large_theory_mode                     true
% 2.11/1.02  --prolific_symb_bound                   200
% 2.11/1.02  --lt_threshold                          2000
% 2.11/1.02  --clause_weak_htbl                      true
% 2.11/1.02  --gc_record_bc_elim                     false
% 2.11/1.02  
% 2.11/1.02  ------ Preprocessing Options
% 2.11/1.02  
% 2.11/1.02  --preprocessing_flag                    true
% 2.11/1.02  --time_out_prep_mult                    0.1
% 2.11/1.02  --splitting_mode                        input
% 2.11/1.02  --splitting_grd                         true
% 2.11/1.02  --splitting_cvd                         false
% 2.11/1.02  --splitting_cvd_svl                     false
% 2.11/1.02  --splitting_nvd                         32
% 2.11/1.02  --sub_typing                            true
% 2.11/1.02  --prep_gs_sim                           true
% 2.11/1.02  --prep_unflatten                        true
% 2.11/1.02  --prep_res_sim                          true
% 2.11/1.02  --prep_upred                            true
% 2.11/1.02  --prep_sem_filter                       exhaustive
% 2.11/1.02  --prep_sem_filter_out                   false
% 2.11/1.02  --pred_elim                             true
% 2.11/1.02  --res_sim_input                         true
% 2.11/1.02  --eq_ax_congr_red                       true
% 2.11/1.02  --pure_diseq_elim                       true
% 2.11/1.02  --brand_transform                       false
% 2.11/1.02  --non_eq_to_eq                          false
% 2.11/1.02  --prep_def_merge                        true
% 2.11/1.02  --prep_def_merge_prop_impl              false
% 2.11/1.02  --prep_def_merge_mbd                    true
% 2.11/1.02  --prep_def_merge_tr_red                 false
% 2.11/1.02  --prep_def_merge_tr_cl                  false
% 2.11/1.02  --smt_preprocessing                     true
% 2.11/1.02  --smt_ac_axioms                         fast
% 2.11/1.02  --preprocessed_out                      false
% 2.11/1.02  --preprocessed_stats                    false
% 2.11/1.02  
% 2.11/1.02  ------ Abstraction refinement Options
% 2.11/1.02  
% 2.11/1.02  --abstr_ref                             []
% 2.11/1.02  --abstr_ref_prep                        false
% 2.11/1.02  --abstr_ref_until_sat                   false
% 2.11/1.02  --abstr_ref_sig_restrict                funpre
% 2.11/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/1.02  --abstr_ref_under                       []
% 2.11/1.02  
% 2.11/1.02  ------ SAT Options
% 2.11/1.02  
% 2.11/1.02  --sat_mode                              false
% 2.11/1.02  --sat_fm_restart_options                ""
% 2.11/1.02  --sat_gr_def                            false
% 2.11/1.02  --sat_epr_types                         true
% 2.11/1.02  --sat_non_cyclic_types                  false
% 2.11/1.02  --sat_finite_models                     false
% 2.11/1.02  --sat_fm_lemmas                         false
% 2.11/1.02  --sat_fm_prep                           false
% 2.11/1.02  --sat_fm_uc_incr                        true
% 2.11/1.02  --sat_out_model                         small
% 2.11/1.02  --sat_out_clauses                       false
% 2.11/1.02  
% 2.11/1.02  ------ QBF Options
% 2.11/1.02  
% 2.11/1.02  --qbf_mode                              false
% 2.11/1.02  --qbf_elim_univ                         false
% 2.11/1.02  --qbf_dom_inst                          none
% 2.11/1.02  --qbf_dom_pre_inst                      false
% 2.11/1.02  --qbf_sk_in                             false
% 2.11/1.02  --qbf_pred_elim                         true
% 2.11/1.02  --qbf_split                             512
% 2.11/1.02  
% 2.11/1.02  ------ BMC1 Options
% 2.11/1.02  
% 2.11/1.02  --bmc1_incremental                      false
% 2.11/1.02  --bmc1_axioms                           reachable_all
% 2.11/1.02  --bmc1_min_bound                        0
% 2.11/1.02  --bmc1_max_bound                        -1
% 2.11/1.02  --bmc1_max_bound_default                -1
% 2.11/1.02  --bmc1_symbol_reachability              true
% 2.11/1.02  --bmc1_property_lemmas                  false
% 2.11/1.02  --bmc1_k_induction                      false
% 2.11/1.02  --bmc1_non_equiv_states                 false
% 2.11/1.02  --bmc1_deadlock                         false
% 2.11/1.02  --bmc1_ucm                              false
% 2.11/1.02  --bmc1_add_unsat_core                   none
% 2.11/1.02  --bmc1_unsat_core_children              false
% 2.11/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/1.02  --bmc1_out_stat                         full
% 2.11/1.02  --bmc1_ground_init                      false
% 2.11/1.02  --bmc1_pre_inst_next_state              false
% 2.11/1.02  --bmc1_pre_inst_state                   false
% 2.11/1.02  --bmc1_pre_inst_reach_state             false
% 2.11/1.02  --bmc1_out_unsat_core                   false
% 2.11/1.02  --bmc1_aig_witness_out                  false
% 2.11/1.02  --bmc1_verbose                          false
% 2.11/1.02  --bmc1_dump_clauses_tptp                false
% 2.11/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.11/1.02  --bmc1_dump_file                        -
% 2.11/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.11/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.11/1.02  --bmc1_ucm_extend_mode                  1
% 2.11/1.02  --bmc1_ucm_init_mode                    2
% 2.11/1.02  --bmc1_ucm_cone_mode                    none
% 2.11/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.11/1.02  --bmc1_ucm_relax_model                  4
% 2.11/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.11/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/1.02  --bmc1_ucm_layered_model                none
% 2.11/1.02  --bmc1_ucm_max_lemma_size               10
% 2.11/1.02  
% 2.11/1.02  ------ AIG Options
% 2.11/1.02  
% 2.11/1.02  --aig_mode                              false
% 2.11/1.02  
% 2.11/1.02  ------ Instantiation Options
% 2.11/1.02  
% 2.11/1.02  --instantiation_flag                    true
% 2.11/1.02  --inst_sos_flag                         false
% 2.11/1.02  --inst_sos_phase                        true
% 2.11/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/1.02  --inst_lit_sel_side                     num_symb
% 2.11/1.02  --inst_solver_per_active                1400
% 2.11/1.02  --inst_solver_calls_frac                1.
% 2.11/1.02  --inst_passive_queue_type               priority_queues
% 2.11/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/1.02  --inst_passive_queues_freq              [25;2]
% 2.11/1.02  --inst_dismatching                      true
% 2.11/1.02  --inst_eager_unprocessed_to_passive     true
% 2.11/1.02  --inst_prop_sim_given                   true
% 2.11/1.02  --inst_prop_sim_new                     false
% 2.11/1.02  --inst_subs_new                         false
% 2.11/1.02  --inst_eq_res_simp                      false
% 2.11/1.02  --inst_subs_given                       false
% 2.11/1.02  --inst_orphan_elimination               true
% 2.11/1.02  --inst_learning_loop_flag               true
% 2.11/1.02  --inst_learning_start                   3000
% 2.11/1.02  --inst_learning_factor                  2
% 2.11/1.02  --inst_start_prop_sim_after_learn       3
% 2.11/1.02  --inst_sel_renew                        solver
% 2.11/1.02  --inst_lit_activity_flag                true
% 2.11/1.02  --inst_restr_to_given                   false
% 2.11/1.02  --inst_activity_threshold               500
% 2.11/1.02  --inst_out_proof                        true
% 2.11/1.02  
% 2.11/1.02  ------ Resolution Options
% 2.11/1.02  
% 2.11/1.02  --resolution_flag                       true
% 2.11/1.02  --res_lit_sel                           adaptive
% 2.11/1.02  --res_lit_sel_side                      none
% 2.11/1.02  --res_ordering                          kbo
% 2.11/1.02  --res_to_prop_solver                    active
% 2.11/1.02  --res_prop_simpl_new                    false
% 2.11/1.02  --res_prop_simpl_given                  true
% 2.11/1.02  --res_passive_queue_type                priority_queues
% 2.11/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/1.02  --res_passive_queues_freq               [15;5]
% 2.11/1.02  --res_forward_subs                      full
% 2.11/1.02  --res_backward_subs                     full
% 2.11/1.02  --res_forward_subs_resolution           true
% 2.11/1.02  --res_backward_subs_resolution          true
% 2.11/1.02  --res_orphan_elimination                true
% 2.11/1.02  --res_time_limit                        2.
% 2.11/1.02  --res_out_proof                         true
% 2.11/1.02  
% 2.11/1.02  ------ Superposition Options
% 2.11/1.02  
% 2.11/1.02  --superposition_flag                    true
% 2.11/1.02  --sup_passive_queue_type                priority_queues
% 2.11/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.11/1.02  --demod_completeness_check              fast
% 2.11/1.02  --demod_use_ground                      true
% 2.11/1.02  --sup_to_prop_solver                    passive
% 2.11/1.02  --sup_prop_simpl_new                    true
% 2.11/1.02  --sup_prop_simpl_given                  true
% 2.11/1.02  --sup_fun_splitting                     false
% 2.11/1.02  --sup_smt_interval                      50000
% 2.11/1.02  
% 2.11/1.02  ------ Superposition Simplification Setup
% 2.11/1.02  
% 2.11/1.02  --sup_indices_passive                   []
% 2.11/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.02  --sup_full_bw                           [BwDemod]
% 2.11/1.02  --sup_immed_triv                        [TrivRules]
% 2.11/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.02  --sup_immed_bw_main                     []
% 2.11/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.02  
% 2.11/1.02  ------ Combination Options
% 2.11/1.02  
% 2.11/1.02  --comb_res_mult                         3
% 2.11/1.02  --comb_sup_mult                         2
% 2.11/1.02  --comb_inst_mult                        10
% 2.11/1.02  
% 2.11/1.02  ------ Debug Options
% 2.11/1.02  
% 2.11/1.02  --dbg_backtrace                         false
% 2.11/1.02  --dbg_dump_prop_clauses                 false
% 2.11/1.02  --dbg_dump_prop_clauses_file            -
% 2.11/1.02  --dbg_out_stat                          false
% 2.11/1.02  ------ Parsing...
% 2.11/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.11/1.02  
% 2.11/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.11/1.02  
% 2.11/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.11/1.02  
% 2.11/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.11/1.02  ------ Proving...
% 2.11/1.02  ------ Problem Properties 
% 2.11/1.02  
% 2.11/1.02  
% 2.11/1.02  clauses                                 23
% 2.11/1.02  conjectures                             3
% 2.11/1.02  EPR                                     9
% 2.11/1.02  Horn                                    17
% 2.11/1.02  unary                                   9
% 2.11/1.02  binary                                  10
% 2.11/1.02  lits                                    41
% 2.11/1.02  lits eq                                 7
% 2.11/1.02  fd_pure                                 0
% 2.11/1.02  fd_pseudo                               0
% 2.11/1.02  fd_cond                                 1
% 2.11/1.02  fd_pseudo_cond                          1
% 2.11/1.02  AC symbols                              0
% 2.11/1.02  
% 2.11/1.02  ------ Schedule dynamic 5 is on 
% 2.11/1.02  
% 2.11/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.11/1.02  
% 2.11/1.02  
% 2.11/1.02  ------ 
% 2.11/1.02  Current options:
% 2.11/1.02  ------ 
% 2.11/1.02  
% 2.11/1.02  ------ Input Options
% 2.11/1.02  
% 2.11/1.02  --out_options                           all
% 2.11/1.02  --tptp_safe_out                         true
% 2.11/1.02  --problem_path                          ""
% 2.11/1.02  --include_path                          ""
% 2.11/1.02  --clausifier                            res/vclausify_rel
% 2.11/1.02  --clausifier_options                    --mode clausify
% 2.11/1.02  --stdin                                 false
% 2.11/1.02  --stats_out                             all
% 2.11/1.02  
% 2.11/1.02  ------ General Options
% 2.11/1.02  
% 2.11/1.02  --fof                                   false
% 2.11/1.02  --time_out_real                         305.
% 2.11/1.02  --time_out_virtual                      -1.
% 2.11/1.02  --symbol_type_check                     false
% 2.11/1.02  --clausify_out                          false
% 2.11/1.02  --sig_cnt_out                           false
% 2.11/1.02  --trig_cnt_out                          false
% 2.11/1.02  --trig_cnt_out_tolerance                1.
% 2.11/1.02  --trig_cnt_out_sk_spl                   false
% 2.11/1.02  --abstr_cl_out                          false
% 2.11/1.02  
% 2.11/1.02  ------ Global Options
% 2.11/1.02  
% 2.11/1.02  --schedule                              default
% 2.11/1.02  --add_important_lit                     false
% 2.11/1.02  --prop_solver_per_cl                    1000
% 2.11/1.02  --min_unsat_core                        false
% 2.11/1.02  --soft_assumptions                      false
% 2.11/1.02  --soft_lemma_size                       3
% 2.11/1.02  --prop_impl_unit_size                   0
% 2.11/1.02  --prop_impl_unit                        []
% 2.11/1.02  --share_sel_clauses                     true
% 2.11/1.02  --reset_solvers                         false
% 2.11/1.02  --bc_imp_inh                            [conj_cone]
% 2.11/1.02  --conj_cone_tolerance                   3.
% 2.11/1.02  --extra_neg_conj                        none
% 2.11/1.02  --large_theory_mode                     true
% 2.11/1.02  --prolific_symb_bound                   200
% 2.11/1.02  --lt_threshold                          2000
% 2.11/1.02  --clause_weak_htbl                      true
% 2.11/1.02  --gc_record_bc_elim                     false
% 2.11/1.02  
% 2.11/1.02  ------ Preprocessing Options
% 2.11/1.02  
% 2.11/1.02  --preprocessing_flag                    true
% 2.11/1.02  --time_out_prep_mult                    0.1
% 2.11/1.02  --splitting_mode                        input
% 2.11/1.02  --splitting_grd                         true
% 2.11/1.02  --splitting_cvd                         false
% 2.11/1.02  --splitting_cvd_svl                     false
% 2.11/1.02  --splitting_nvd                         32
% 2.11/1.02  --sub_typing                            true
% 2.11/1.02  --prep_gs_sim                           true
% 2.11/1.02  --prep_unflatten                        true
% 2.11/1.02  --prep_res_sim                          true
% 2.11/1.02  --prep_upred                            true
% 2.11/1.02  --prep_sem_filter                       exhaustive
% 2.11/1.02  --prep_sem_filter_out                   false
% 2.11/1.02  --pred_elim                             true
% 2.11/1.02  --res_sim_input                         true
% 2.11/1.02  --eq_ax_congr_red                       true
% 2.11/1.02  --pure_diseq_elim                       true
% 2.11/1.02  --brand_transform                       false
% 2.11/1.02  --non_eq_to_eq                          false
% 2.11/1.02  --prep_def_merge                        true
% 2.11/1.02  --prep_def_merge_prop_impl              false
% 2.11/1.02  --prep_def_merge_mbd                    true
% 2.11/1.02  --prep_def_merge_tr_red                 false
% 2.11/1.02  --prep_def_merge_tr_cl                  false
% 2.11/1.02  --smt_preprocessing                     true
% 2.11/1.02  --smt_ac_axioms                         fast
% 2.11/1.02  --preprocessed_out                      false
% 2.11/1.02  --preprocessed_stats                    false
% 2.11/1.02  
% 2.11/1.02  ------ Abstraction refinement Options
% 2.11/1.02  
% 2.11/1.02  --abstr_ref                             []
% 2.11/1.02  --abstr_ref_prep                        false
% 2.11/1.02  --abstr_ref_until_sat                   false
% 2.11/1.02  --abstr_ref_sig_restrict                funpre
% 2.11/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/1.02  --abstr_ref_under                       []
% 2.11/1.02  
% 2.11/1.02  ------ SAT Options
% 2.11/1.02  
% 2.11/1.02  --sat_mode                              false
% 2.11/1.02  --sat_fm_restart_options                ""
% 2.11/1.02  --sat_gr_def                            false
% 2.11/1.02  --sat_epr_types                         true
% 2.11/1.02  --sat_non_cyclic_types                  false
% 2.11/1.02  --sat_finite_models                     false
% 2.11/1.02  --sat_fm_lemmas                         false
% 2.11/1.02  --sat_fm_prep                           false
% 2.11/1.02  --sat_fm_uc_incr                        true
% 2.11/1.02  --sat_out_model                         small
% 2.11/1.02  --sat_out_clauses                       false
% 2.11/1.02  
% 2.11/1.02  ------ QBF Options
% 2.11/1.02  
% 2.11/1.02  --qbf_mode                              false
% 2.11/1.02  --qbf_elim_univ                         false
% 2.11/1.02  --qbf_dom_inst                          none
% 2.11/1.02  --qbf_dom_pre_inst                      false
% 2.11/1.02  --qbf_sk_in                             false
% 2.11/1.02  --qbf_pred_elim                         true
% 2.11/1.02  --qbf_split                             512
% 2.11/1.02  
% 2.11/1.02  ------ BMC1 Options
% 2.11/1.02  
% 2.11/1.02  --bmc1_incremental                      false
% 2.11/1.02  --bmc1_axioms                           reachable_all
% 2.11/1.02  --bmc1_min_bound                        0
% 2.11/1.02  --bmc1_max_bound                        -1
% 2.11/1.02  --bmc1_max_bound_default                -1
% 2.11/1.02  --bmc1_symbol_reachability              true
% 2.11/1.02  --bmc1_property_lemmas                  false
% 2.11/1.02  --bmc1_k_induction                      false
% 2.11/1.02  --bmc1_non_equiv_states                 false
% 2.11/1.02  --bmc1_deadlock                         false
% 2.11/1.02  --bmc1_ucm                              false
% 2.11/1.02  --bmc1_add_unsat_core                   none
% 2.11/1.02  --bmc1_unsat_core_children              false
% 2.11/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/1.02  --bmc1_out_stat                         full
% 2.11/1.02  --bmc1_ground_init                      false
% 2.11/1.02  --bmc1_pre_inst_next_state              false
% 2.11/1.02  --bmc1_pre_inst_state                   false
% 2.11/1.02  --bmc1_pre_inst_reach_state             false
% 2.11/1.02  --bmc1_out_unsat_core                   false
% 2.11/1.02  --bmc1_aig_witness_out                  false
% 2.11/1.02  --bmc1_verbose                          false
% 2.11/1.02  --bmc1_dump_clauses_tptp                false
% 2.11/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.11/1.02  --bmc1_dump_file                        -
% 2.11/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.11/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.11/1.02  --bmc1_ucm_extend_mode                  1
% 2.11/1.02  --bmc1_ucm_init_mode                    2
% 2.11/1.02  --bmc1_ucm_cone_mode                    none
% 2.11/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.11/1.02  --bmc1_ucm_relax_model                  4
% 2.11/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.11/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/1.02  --bmc1_ucm_layered_model                none
% 2.11/1.02  --bmc1_ucm_max_lemma_size               10
% 2.11/1.02  
% 2.11/1.02  ------ AIG Options
% 2.11/1.02  
% 2.11/1.02  --aig_mode                              false
% 2.11/1.02  
% 2.11/1.02  ------ Instantiation Options
% 2.11/1.02  
% 2.11/1.02  --instantiation_flag                    true
% 2.11/1.02  --inst_sos_flag                         false
% 2.11/1.02  --inst_sos_phase                        true
% 2.11/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/1.02  --inst_lit_sel_side                     none
% 2.11/1.02  --inst_solver_per_active                1400
% 2.11/1.02  --inst_solver_calls_frac                1.
% 2.11/1.02  --inst_passive_queue_type               priority_queues
% 2.11/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/1.02  --inst_passive_queues_freq              [25;2]
% 2.11/1.02  --inst_dismatching                      true
% 2.11/1.02  --inst_eager_unprocessed_to_passive     true
% 2.11/1.02  --inst_prop_sim_given                   true
% 2.11/1.02  --inst_prop_sim_new                     false
% 2.11/1.02  --inst_subs_new                         false
% 2.11/1.02  --inst_eq_res_simp                      false
% 2.11/1.02  --inst_subs_given                       false
% 2.11/1.02  --inst_orphan_elimination               true
% 2.11/1.02  --inst_learning_loop_flag               true
% 2.11/1.02  --inst_learning_start                   3000
% 2.11/1.02  --inst_learning_factor                  2
% 2.11/1.02  --inst_start_prop_sim_after_learn       3
% 2.11/1.02  --inst_sel_renew                        solver
% 2.11/1.02  --inst_lit_activity_flag                true
% 2.11/1.02  --inst_restr_to_given                   false
% 2.11/1.02  --inst_activity_threshold               500
% 2.11/1.02  --inst_out_proof                        true
% 2.11/1.02  
% 2.11/1.02  ------ Resolution Options
% 2.11/1.02  
% 2.11/1.02  --resolution_flag                       false
% 2.11/1.02  --res_lit_sel                           adaptive
% 2.11/1.02  --res_lit_sel_side                      none
% 2.11/1.02  --res_ordering                          kbo
% 2.11/1.02  --res_to_prop_solver                    active
% 2.11/1.02  --res_prop_simpl_new                    false
% 2.11/1.02  --res_prop_simpl_given                  true
% 2.11/1.02  --res_passive_queue_type                priority_queues
% 2.11/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/1.02  --res_passive_queues_freq               [15;5]
% 2.11/1.02  --res_forward_subs                      full
% 2.11/1.02  --res_backward_subs                     full
% 2.11/1.02  --res_forward_subs_resolution           true
% 2.11/1.02  --res_backward_subs_resolution          true
% 2.11/1.02  --res_orphan_elimination                true
% 2.11/1.02  --res_time_limit                        2.
% 2.11/1.02  --res_out_proof                         true
% 2.11/1.02  
% 2.11/1.02  ------ Superposition Options
% 2.11/1.02  
% 2.11/1.02  --superposition_flag                    true
% 2.11/1.02  --sup_passive_queue_type                priority_queues
% 2.11/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.11/1.02  --demod_completeness_check              fast
% 2.11/1.02  --demod_use_ground                      true
% 2.11/1.02  --sup_to_prop_solver                    passive
% 2.11/1.02  --sup_prop_simpl_new                    true
% 2.11/1.02  --sup_prop_simpl_given                  true
% 2.11/1.02  --sup_fun_splitting                     false
% 2.11/1.02  --sup_smt_interval                      50000
% 2.11/1.02  
% 2.11/1.02  ------ Superposition Simplification Setup
% 2.11/1.02  
% 2.11/1.02  --sup_indices_passive                   []
% 2.11/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.02  --sup_full_bw                           [BwDemod]
% 2.11/1.02  --sup_immed_triv                        [TrivRules]
% 2.11/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.02  --sup_immed_bw_main                     []
% 2.11/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.02  
% 2.11/1.02  ------ Combination Options
% 2.11/1.02  
% 2.11/1.02  --comb_res_mult                         3
% 2.11/1.02  --comb_sup_mult                         2
% 2.11/1.02  --comb_inst_mult                        10
% 2.11/1.02  
% 2.11/1.02  ------ Debug Options
% 2.11/1.02  
% 2.11/1.02  --dbg_backtrace                         false
% 2.11/1.02  --dbg_dump_prop_clauses                 false
% 2.11/1.02  --dbg_dump_prop_clauses_file            -
% 2.11/1.02  --dbg_out_stat                          false
% 2.11/1.02  
% 2.11/1.02  
% 2.11/1.02  
% 2.11/1.02  
% 2.11/1.02  ------ Proving...
% 2.11/1.02  
% 2.11/1.02  
% 2.11/1.02  % SZS status Theorem for theBenchmark.p
% 2.11/1.02  
% 2.11/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.11/1.02  
% 2.11/1.02  fof(f8,axiom,(
% 2.11/1.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.11/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.02  
% 2.11/1.02  fof(f62,plain,(
% 2.11/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.11/1.02    inference(cnf_transformation,[],[f8])).
% 2.11/1.02  
% 2.11/1.02  fof(f16,axiom,(
% 2.11/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.11/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.02  
% 2.11/1.02  fof(f24,plain,(
% 2.11/1.02    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.11/1.02    inference(ennf_transformation,[],[f16])).
% 2.11/1.02  
% 2.11/1.02  fof(f25,plain,(
% 2.11/1.02    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.11/1.02    inference(flattening,[],[f24])).
% 2.11/1.02  
% 2.11/1.02  fof(f70,plain,(
% 2.11/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.11/1.02    inference(cnf_transformation,[],[f25])).
% 2.11/1.02  
% 2.11/1.02  fof(f17,conjecture,(
% 2.11/1.02    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 2.11/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.02  
% 2.11/1.02  fof(f18,negated_conjecture,(
% 2.11/1.02    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 2.11/1.02    inference(negated_conjecture,[],[f17])).
% 2.11/1.02  
% 2.11/1.02  fof(f26,plain,(
% 2.11/1.02    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 2.11/1.02    inference(ennf_transformation,[],[f18])).
% 2.11/1.02  
% 2.11/1.02  fof(f27,plain,(
% 2.11/1.02    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 2.11/1.02    inference(flattening,[],[f26])).
% 2.11/1.02  
% 2.11/1.02  fof(f44,plain,(
% 2.11/1.02    ( ! [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) => (~r1_tarski(X0,sK5) & ~v1_xboole_0(k3_xboole_0(X0,sK5)))) )),
% 2.11/1.02    introduced(choice_axiom,[])).
% 2.11/1.02  
% 2.11/1.02  fof(f43,plain,(
% 2.11/1.02    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK4,X1) & ~v1_xboole_0(k3_xboole_0(sK4,X1))) & v1_zfmisc_1(sK4) & ~v1_xboole_0(sK4))),
% 2.11/1.02    introduced(choice_axiom,[])).
% 2.11/1.02  
% 2.11/1.02  fof(f45,plain,(
% 2.11/1.02    (~r1_tarski(sK4,sK5) & ~v1_xboole_0(k3_xboole_0(sK4,sK5))) & v1_zfmisc_1(sK4) & ~v1_xboole_0(sK4)),
% 2.11/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f44,f43])).
% 2.11/1.02  
% 2.11/1.02  fof(f72,plain,(
% 2.11/1.02    v1_zfmisc_1(sK4)),
% 2.11/1.02    inference(cnf_transformation,[],[f45])).
% 2.11/1.02  
% 2.11/1.02  fof(f71,plain,(
% 2.11/1.02    ~v1_xboole_0(sK4)),
% 2.11/1.02    inference(cnf_transformation,[],[f45])).
% 2.11/1.02  
% 2.11/1.02  fof(f2,axiom,(
% 2.11/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.11/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.02  
% 2.11/1.02  fof(f21,plain,(
% 2.11/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.11/1.02    inference(ennf_transformation,[],[f2])).
% 2.11/1.02  
% 2.11/1.02  fof(f32,plain,(
% 2.11/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/1.02    inference(nnf_transformation,[],[f21])).
% 2.11/1.02  
% 2.11/1.02  fof(f33,plain,(
% 2.11/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/1.02    inference(rectify,[],[f32])).
% 2.11/1.02  
% 2.11/1.02  fof(f34,plain,(
% 2.11/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.11/1.02    introduced(choice_axiom,[])).
% 2.11/1.02  
% 2.11/1.02  fof(f35,plain,(
% 2.11/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 2.11/1.02  
% 2.11/1.02  fof(f49,plain,(
% 2.11/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.11/1.02    inference(cnf_transformation,[],[f35])).
% 2.11/1.02  
% 2.11/1.02  fof(f1,axiom,(
% 2.11/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.11/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.02  
% 2.11/1.02  fof(f28,plain,(
% 2.11/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.11/1.02    inference(nnf_transformation,[],[f1])).
% 2.11/1.02  
% 2.11/1.02  fof(f29,plain,(
% 2.11/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.11/1.02    inference(rectify,[],[f28])).
% 2.11/1.02  
% 2.11/1.02  fof(f30,plain,(
% 2.11/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.11/1.02    introduced(choice_axiom,[])).
% 2.11/1.02  
% 2.11/1.02  fof(f31,plain,(
% 2.11/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.11/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.11/1.02  
% 2.11/1.02  fof(f46,plain,(
% 2.11/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.11/1.02    inference(cnf_transformation,[],[f31])).
% 2.11/1.02  
% 2.11/1.02  fof(f7,axiom,(
% 2.11/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.11/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.02  
% 2.11/1.02  fof(f61,plain,(
% 2.11/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.11/1.02    inference(cnf_transformation,[],[f7])).
% 2.11/1.02  
% 2.11/1.02  fof(f5,axiom,(
% 2.11/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.11/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.02  
% 2.11/1.02  fof(f40,plain,(
% 2.11/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/1.02    inference(nnf_transformation,[],[f5])).
% 2.11/1.02  
% 2.11/1.02  fof(f41,plain,(
% 2.11/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/1.02    inference(flattening,[],[f40])).
% 2.11/1.02  
% 2.11/1.02  fof(f58,plain,(
% 2.11/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.11/1.02    inference(cnf_transformation,[],[f41])).
% 2.11/1.02  
% 2.11/1.02  fof(f73,plain,(
% 2.11/1.02    ~v1_xboole_0(k3_xboole_0(sK4,sK5))),
% 2.11/1.02    inference(cnf_transformation,[],[f45])).
% 2.11/1.02  
% 2.11/1.02  fof(f10,axiom,(
% 2.11/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.11/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.02  
% 2.11/1.02  fof(f64,plain,(
% 2.11/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.11/1.02    inference(cnf_transformation,[],[f10])).
% 2.11/1.02  
% 2.11/1.02  fof(f81,plain,(
% 2.11/1.02    ~v1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)))),
% 2.11/1.02    inference(definition_unfolding,[],[f73,f64])).
% 2.11/1.02  
% 2.11/1.02  fof(f57,plain,(
% 2.11/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.11/1.02    inference(cnf_transformation,[],[f41])).
% 2.11/1.02  
% 2.11/1.02  fof(f82,plain,(
% 2.11/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.11/1.02    inference(equality_resolution,[],[f57])).
% 2.11/1.02  
% 2.11/1.02  fof(f6,axiom,(
% 2.11/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.11/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.02  
% 2.11/1.02  fof(f42,plain,(
% 2.11/1.02    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.11/1.02    inference(nnf_transformation,[],[f6])).
% 2.11/1.02  
% 2.11/1.02  fof(f60,plain,(
% 2.11/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.11/1.02    inference(cnf_transformation,[],[f42])).
% 2.11/1.02  
% 2.11/1.02  fof(f59,plain,(
% 2.11/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.11/1.02    inference(cnf_transformation,[],[f42])).
% 2.11/1.02  
% 2.11/1.02  fof(f74,plain,(
% 2.11/1.02    ~r1_tarski(sK4,sK5)),
% 2.11/1.02    inference(cnf_transformation,[],[f45])).
% 2.11/1.02  
% 2.11/1.02  cnf(c_16,plain,
% 2.11/1.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.11/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1219,plain,
% 2.11/1.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.11/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_20,plain,
% 2.11/1.02      ( ~ r1_tarski(X0,X1)
% 2.11/1.02      | ~ v1_zfmisc_1(X1)
% 2.11/1.02      | v1_xboole_0(X0)
% 2.11/1.02      | v1_xboole_0(X1)
% 2.11/1.02      | X1 = X0 ),
% 2.11/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_23,negated_conjecture,
% 2.11/1.02      ( v1_zfmisc_1(sK4) ),
% 2.11/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_282,plain,
% 2.11/1.02      ( ~ r1_tarski(X0,X1)
% 2.11/1.02      | v1_xboole_0(X0)
% 2.11/1.02      | v1_xboole_0(X1)
% 2.11/1.02      | X1 = X0
% 2.11/1.02      | sK4 != X1 ),
% 2.11/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_23]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_283,plain,
% 2.11/1.02      ( ~ r1_tarski(X0,sK4)
% 2.11/1.02      | v1_xboole_0(X0)
% 2.11/1.02      | v1_xboole_0(sK4)
% 2.11/1.02      | sK4 = X0 ),
% 2.11/1.02      inference(unflattening,[status(thm)],[c_282]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_24,negated_conjecture,
% 2.11/1.02      ( ~ v1_xboole_0(sK4) ),
% 2.11/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_285,plain,
% 2.11/1.02      ( v1_xboole_0(X0) | ~ r1_tarski(X0,sK4) | sK4 = X0 ),
% 2.11/1.02      inference(global_propositional_subsumption,
% 2.11/1.02                [status(thm)],
% 2.11/1.02                [c_283,c_24]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_286,plain,
% 2.11/1.02      ( ~ r1_tarski(X0,sK4) | v1_xboole_0(X0) | sK4 = X0 ),
% 2.11/1.02      inference(renaming,[status(thm)],[c_285]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1215,plain,
% 2.11/1.02      ( sK4 = X0
% 2.11/1.02      | r1_tarski(X0,sK4) != iProver_top
% 2.11/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.11/1.02      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1785,plain,
% 2.11/1.02      ( k4_xboole_0(sK4,X0) = sK4
% 2.11/1.02      | v1_xboole_0(k4_xboole_0(sK4,X0)) = iProver_top ),
% 2.11/1.02      inference(superposition,[status(thm)],[c_1219,c_1215]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_3,plain,
% 2.11/1.02      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.11/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1231,plain,
% 2.11/1.02      ( r1_tarski(X0,X1) = iProver_top
% 2.11/1.02      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.11/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1,plain,
% 2.11/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.11/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1233,plain,
% 2.11/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.11/1.02      | v1_xboole_0(X1) != iProver_top ),
% 2.11/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_2561,plain,
% 2.11/1.02      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.11/1.02      inference(superposition,[status(thm)],[c_1231,c_1233]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_15,plain,
% 2.11/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 2.11/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1220,plain,
% 2.11/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.11/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_10,plain,
% 2.11/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.11/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1224,plain,
% 2.11/1.02      ( X0 = X1
% 2.11/1.02      | r1_tarski(X1,X0) != iProver_top
% 2.11/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 2.11/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_2351,plain,
% 2.11/1.02      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.11/1.02      inference(superposition,[status(thm)],[c_1220,c_1224]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_2789,plain,
% 2.11/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.11/1.02      inference(superposition,[status(thm)],[c_2561,c_2351]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_2855,plain,
% 2.11/1.02      ( k4_xboole_0(sK4,X0) = sK4 | k4_xboole_0(sK4,X0) = k1_xboole_0 ),
% 2.11/1.02      inference(superposition,[status(thm)],[c_1785,c_2789]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_22,negated_conjecture,
% 2.11/1.02      ( ~ v1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) ),
% 2.11/1.02      inference(cnf_transformation,[],[f81]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1217,plain,
% 2.11/1.02      ( v1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) != iProver_top ),
% 2.11/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1951,plain,
% 2.11/1.02      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = sK4 ),
% 2.11/1.02      inference(superposition,[status(thm)],[c_1785,c_1217]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_2866,plain,
% 2.11/1.02      ( k4_xboole_0(sK4,sK5) = k1_xboole_0 | k4_xboole_0(sK4,sK4) = sK4 ),
% 2.11/1.02      inference(superposition,[status(thm)],[c_2855,c_1951]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_11,plain,
% 2.11/1.02      ( r1_tarski(X0,X0) ),
% 2.11/1.02      inference(cnf_transformation,[],[f82]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1223,plain,
% 2.11/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 2.11/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_13,plain,
% 2.11/1.02      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.11/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1222,plain,
% 2.11/1.02      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.11/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 2.11/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_2195,plain,
% 2.11/1.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.11/1.02      inference(superposition,[status(thm)],[c_1223,c_1222]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_2874,plain,
% 2.11/1.02      ( k4_xboole_0(sK4,sK5) = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 2.11/1.02      inference(demodulation,[status(thm)],[c_2866,c_2195]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1590,plain,
% 2.11/1.02      ( r1_tarski(k1_xboole_0,sK5) ),
% 2.11/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_761,plain,
% 2.11/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.11/1.02      theory(equality) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1392,plain,
% 2.11/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,sK5) | sK5 != X1 | sK4 != X0 ),
% 2.11/1.02      inference(instantiation,[status(thm)],[c_761]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1435,plain,
% 2.11/1.02      ( ~ r1_tarski(X0,sK5)
% 2.11/1.02      | r1_tarski(sK4,sK5)
% 2.11/1.02      | sK5 != sK5
% 2.11/1.02      | sK4 != X0 ),
% 2.11/1.02      inference(instantiation,[status(thm)],[c_1392]) ).
% 2.11/1.02  
% 2.11/1.02  cnf(c_1589,plain,
% 2.11/1.02      ( r1_tarski(sK4,sK5)
% 2.11/1.02      | ~ r1_tarski(k1_xboole_0,sK5)
% 2.11/1.02      | sK5 != sK5
% 2.11/1.02      | sK4 != k1_xboole_0 ),
% 2.11/1.02      inference(instantiation,[status(thm)],[c_1435]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_757,plain,( X0 = X0 ),theory(equality) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1436,plain,
% 2.11/1.03      ( sK5 = sK5 ),
% 2.11/1.03      inference(instantiation,[status(thm)],[c_757]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_14,plain,
% 2.11/1.03      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.11/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_1364,plain,
% 2.11/1.03      ( r1_tarski(sK4,sK5) | k4_xboole_0(sK4,sK5) != k1_xboole_0 ),
% 2.11/1.03      inference(instantiation,[status(thm)],[c_14]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(c_21,negated_conjecture,
% 2.11/1.03      ( ~ r1_tarski(sK4,sK5) ),
% 2.11/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.11/1.03  
% 2.11/1.03  cnf(contradiction,plain,
% 2.11/1.03      ( $false ),
% 2.11/1.03      inference(minisat,
% 2.11/1.03                [status(thm)],
% 2.11/1.03                [c_2874,c_1590,c_1589,c_1436,c_1364,c_21]) ).
% 2.11/1.03  
% 2.11/1.03  
% 2.11/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.11/1.03  
% 2.11/1.03  ------                               Statistics
% 2.11/1.03  
% 2.11/1.03  ------ General
% 2.11/1.03  
% 2.11/1.03  abstr_ref_over_cycles:                  0
% 2.11/1.03  abstr_ref_under_cycles:                 0
% 2.11/1.03  gc_basic_clause_elim:                   0
% 2.11/1.03  forced_gc_time:                         0
% 2.11/1.03  parsing_time:                           0.023
% 2.11/1.03  unif_index_cands_time:                  0.
% 2.11/1.03  unif_index_add_time:                    0.
% 2.11/1.03  orderings_time:                         0.
% 2.11/1.03  out_proof_time:                         0.011
% 2.11/1.03  total_time:                             0.142
% 2.11/1.03  num_of_symbols:                         46
% 2.11/1.03  num_of_terms:                           2359
% 2.11/1.03  
% 2.11/1.03  ------ Preprocessing
% 2.11/1.03  
% 2.11/1.03  num_of_splits:                          0
% 2.11/1.03  num_of_split_atoms:                     0
% 2.11/1.03  num_of_reused_defs:                     0
% 2.11/1.03  num_eq_ax_congr_red:                    42
% 2.11/1.03  num_of_sem_filtered_clauses:            1
% 2.11/1.03  num_of_subtypes:                        0
% 2.11/1.03  monotx_restored_types:                  0
% 2.11/1.03  sat_num_of_epr_types:                   0
% 2.11/1.03  sat_num_of_non_cyclic_types:            0
% 2.11/1.03  sat_guarded_non_collapsed_types:        0
% 2.11/1.03  num_pure_diseq_elim:                    0
% 2.11/1.03  simp_replaced_by:                       0
% 2.11/1.03  res_preprocessed:                       108
% 2.11/1.03  prep_upred:                             0
% 2.11/1.03  prep_unflattend:                        13
% 2.11/1.03  smt_new_axioms:                         0
% 2.11/1.03  pred_elim_cands:                        4
% 2.11/1.03  pred_elim:                              1
% 2.11/1.03  pred_elim_cl:                           1
% 2.11/1.03  pred_elim_cycles:                       5
% 2.11/1.03  merged_defs:                            8
% 2.11/1.03  merged_defs_ncl:                        0
% 2.11/1.03  bin_hyper_res:                          8
% 2.11/1.03  prep_cycles:                            4
% 2.11/1.03  pred_elim_time:                         0.004
% 2.11/1.03  splitting_time:                         0.
% 2.11/1.03  sem_filter_time:                        0.
% 2.11/1.03  monotx_time:                            0.
% 2.11/1.03  subtype_inf_time:                       0.
% 2.11/1.03  
% 2.11/1.03  ------ Problem properties
% 2.11/1.03  
% 2.11/1.03  clauses:                                23
% 2.11/1.03  conjectures:                            3
% 2.11/1.03  epr:                                    9
% 2.11/1.03  horn:                                   17
% 2.11/1.03  ground:                                 3
% 2.11/1.03  unary:                                  9
% 2.11/1.03  binary:                                 10
% 2.11/1.03  lits:                                   41
% 2.11/1.03  lits_eq:                                7
% 2.11/1.03  fd_pure:                                0
% 2.11/1.03  fd_pseudo:                              0
% 2.11/1.03  fd_cond:                                1
% 2.11/1.03  fd_pseudo_cond:                         1
% 2.11/1.03  ac_symbols:                             0
% 2.11/1.03  
% 2.11/1.03  ------ Propositional Solver
% 2.11/1.03  
% 2.11/1.03  prop_solver_calls:                      26
% 2.11/1.03  prop_fast_solver_calls:                 527
% 2.11/1.03  smt_solver_calls:                       0
% 2.11/1.03  smt_fast_solver_calls:                  0
% 2.11/1.03  prop_num_of_clauses:                    952
% 2.11/1.03  prop_preprocess_simplified:             4401
% 2.11/1.03  prop_fo_subsumed:                       3
% 2.11/1.03  prop_solver_time:                       0.
% 2.11/1.03  smt_solver_time:                        0.
% 2.11/1.03  smt_fast_solver_time:                   0.
% 2.11/1.03  prop_fast_solver_time:                  0.
% 2.11/1.03  prop_unsat_core_time:                   0.
% 2.11/1.03  
% 2.11/1.03  ------ QBF
% 2.11/1.03  
% 2.11/1.03  qbf_q_res:                              0
% 2.11/1.03  qbf_num_tautologies:                    0
% 2.11/1.03  qbf_prep_cycles:                        0
% 2.11/1.03  
% 2.11/1.03  ------ BMC1
% 2.11/1.03  
% 2.11/1.03  bmc1_current_bound:                     -1
% 2.11/1.03  bmc1_last_solved_bound:                 -1
% 2.11/1.03  bmc1_unsat_core_size:                   -1
% 2.11/1.03  bmc1_unsat_core_parents_size:           -1
% 2.11/1.03  bmc1_merge_next_fun:                    0
% 2.11/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.11/1.03  
% 2.11/1.03  ------ Instantiation
% 2.11/1.03  
% 2.11/1.03  inst_num_of_clauses:                    286
% 2.11/1.03  inst_num_in_passive:                    114
% 2.11/1.03  inst_num_in_active:                     137
% 2.11/1.03  inst_num_in_unprocessed:                35
% 2.11/1.03  inst_num_of_loops:                      160
% 2.11/1.03  inst_num_of_learning_restarts:          0
% 2.11/1.03  inst_num_moves_active_passive:          21
% 2.11/1.03  inst_lit_activity:                      0
% 2.11/1.03  inst_lit_activity_moves:                0
% 2.11/1.03  inst_num_tautologies:                   0
% 2.11/1.03  inst_num_prop_implied:                  0
% 2.11/1.03  inst_num_existing_simplified:           0
% 2.11/1.03  inst_num_eq_res_simplified:             0
% 2.11/1.03  inst_num_child_elim:                    0
% 2.11/1.03  inst_num_of_dismatching_blockings:      36
% 2.11/1.03  inst_num_of_non_proper_insts:           193
% 2.11/1.03  inst_num_of_duplicates:                 0
% 2.11/1.03  inst_inst_num_from_inst_to_res:         0
% 2.11/1.03  inst_dismatching_checking_time:         0.
% 2.11/1.03  
% 2.11/1.03  ------ Resolution
% 2.11/1.03  
% 2.11/1.03  res_num_of_clauses:                     0
% 2.11/1.03  res_num_in_passive:                     0
% 2.11/1.03  res_num_in_active:                      0
% 2.11/1.03  res_num_of_loops:                       112
% 2.11/1.03  res_forward_subset_subsumed:            12
% 2.11/1.03  res_backward_subset_subsumed:           6
% 2.11/1.03  res_forward_subsumed:                   0
% 2.11/1.03  res_backward_subsumed:                  0
% 2.11/1.03  res_forward_subsumption_resolution:     1
% 2.11/1.03  res_backward_subsumption_resolution:    0
% 2.11/1.03  res_clause_to_clause_subsumption:       122
% 2.11/1.03  res_orphan_elimination:                 0
% 2.11/1.03  res_tautology_del:                      29
% 2.11/1.03  res_num_eq_res_simplified:              0
% 2.11/1.03  res_num_sel_changes:                    0
% 2.11/1.03  res_moves_from_active_to_pass:          0
% 2.11/1.03  
% 2.11/1.03  ------ Superposition
% 2.11/1.03  
% 2.11/1.03  sup_time_total:                         0.
% 2.11/1.03  sup_time_generating:                    0.
% 2.11/1.03  sup_time_sim_full:                      0.
% 2.11/1.03  sup_time_sim_immed:                     0.
% 2.11/1.03  
% 2.11/1.03  sup_num_of_clauses:                     43
% 2.11/1.03  sup_num_in_active:                      31
% 2.11/1.03  sup_num_in_passive:                     12
% 2.11/1.03  sup_num_of_loops:                       31
% 2.11/1.03  sup_fw_superposition:                   22
% 2.11/1.03  sup_bw_superposition:                   32
% 2.11/1.03  sup_immediate_simplified:               16
% 2.11/1.03  sup_given_eliminated:                   0
% 2.11/1.03  comparisons_done:                       0
% 2.11/1.03  comparisons_avoided:                    0
% 2.11/1.03  
% 2.11/1.03  ------ Simplifications
% 2.11/1.03  
% 2.11/1.03  
% 2.11/1.03  sim_fw_subset_subsumed:                 3
% 2.11/1.03  sim_bw_subset_subsumed:                 0
% 2.11/1.03  sim_fw_subsumed:                        8
% 2.11/1.03  sim_bw_subsumed:                        0
% 2.11/1.03  sim_fw_subsumption_res:                 0
% 2.11/1.03  sim_bw_subsumption_res:                 0
% 2.11/1.03  sim_tautology_del:                      2
% 2.11/1.03  sim_eq_tautology_del:                   6
% 2.11/1.03  sim_eq_res_simp:                        0
% 2.11/1.03  sim_fw_demodulated:                     5
% 2.11/1.03  sim_bw_demodulated:                     1
% 2.11/1.03  sim_light_normalised:                   0
% 2.11/1.03  sim_joinable_taut:                      0
% 2.11/1.03  sim_joinable_simp:                      0
% 2.11/1.03  sim_ac_normalised:                      0
% 2.11/1.03  sim_smt_subsumption:                    0
% 2.11/1.03  
%------------------------------------------------------------------------------
