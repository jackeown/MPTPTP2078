%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:34 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 146 expanded)
%              Number of clauses        :   40 (  52 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  155 ( 259 expanded)
%              Number of equality atoms :   31 (  69 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f19,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f30])).

fof(f52,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f62,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(definition_unfolding,[],[f52,f53,f53])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

cnf(c_162,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1069,plain,
    ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
    | r1_tarski(X3,k3_xboole_0(X2,X1))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_162,c_0])).

cnf(c_6,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4274,plain,
    ( r1_tarski(X0,k3_xboole_0(X1,X2))
    | X0 != k3_xboole_0(k3_xboole_0(X2,X1),X3) ),
    inference(resolution,[status(thm)],[c_1069,c_6])).

cnf(c_8538,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_4274,c_0])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8561,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X2) ),
    inference(resolution,[status(thm)],[c_8538,c_7])).

cnf(c_160,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_159,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1054,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_160,c_159])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2439,plain,
    ( ~ r1_tarski(X0,X1)
    | X0 = k3_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_1054,c_8])).

cnf(c_1077,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_162,c_159])).

cnf(c_3122,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_2439,c_1077])).

cnf(c_9312,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_8561,c_3122])).

cnf(c_1073,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X3,k3_xboole_0(X1,X2))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_162,c_8])).

cnf(c_6567,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_1073,c_159])).

cnf(c_10928,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(resolution,[status(thm)],[c_9312,c_6567])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13130,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k1_zfmisc_1(X0))
    | r1_tarski(X2,k1_zfmisc_1(X1)) ),
    inference(resolution,[status(thm)],[c_10928,c_11])).

cnf(c_32723,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(k1_zfmisc_1(X0),X2),k1_zfmisc_1(X1)) ),
    inference(resolution,[status(thm)],[c_13130,c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_858,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
    | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(resolution,[status(thm)],[c_5,c_12])).

cnf(c_446,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
    | r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
    | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_485,plain,
    ( r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
    | ~ r1_tarski(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_574,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1084,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_858,c_12,c_446,c_485,c_574])).

cnf(c_1324,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
    | ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(resolution,[status(thm)],[c_1084,c_5])).

cnf(c_33998,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
    | ~ r1_tarski(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) ),
    inference(resolution,[status(thm)],[c_32723,c_1324])).

cnf(c_2998,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6876,plain,
    ( r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
    | ~ r1_tarski(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) ),
    inference(instantiation,[status(thm)],[c_2998])).

cnf(c_34009,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33998,c_6876])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_34021,plain,
    ( ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[status(thm)],[c_34009,c_4])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_7331,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34021,c_7331])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:33:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  % Running in FOF mode
% 7.85/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/1.51  
% 7.85/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.85/1.51  
% 7.85/1.51  ------  iProver source info
% 7.85/1.51  
% 7.85/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.85/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.85/1.51  git: non_committed_changes: false
% 7.85/1.51  git: last_make_outside_of_git: false
% 7.85/1.51  
% 7.85/1.51  ------ 
% 7.85/1.51  ------ Parsing...
% 7.85/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.85/1.51  
% 7.85/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.85/1.51  
% 7.85/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.85/1.51  
% 7.85/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.85/1.51  ------ Proving...
% 7.85/1.51  ------ Problem Properties 
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  clauses                                 12
% 7.85/1.51  conjectures                             1
% 7.85/1.51  EPR                                     2
% 7.85/1.51  Horn                                    12
% 7.85/1.51  unary                                   6
% 7.85/1.51  binary                                  4
% 7.85/1.51  lits                                    20
% 7.85/1.51  lits eq                                 4
% 7.85/1.51  fd_pure                                 0
% 7.85/1.51  fd_pseudo                               0
% 7.85/1.51  fd_cond                                 0
% 7.85/1.51  fd_pseudo_cond                          1
% 7.85/1.51  AC symbols                              0
% 7.85/1.51  
% 7.85/1.51  ------ Input Options Time Limit: Unbounded
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  ------ 
% 7.85/1.51  Current options:
% 7.85/1.51  ------ 
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  ------ Proving...
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  % SZS status Theorem for theBenchmark.p
% 7.85/1.51  
% 7.85/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.85/1.51  
% 7.85/1.51  fof(f1,axiom,(
% 7.85/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f32,plain,(
% 7.85/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f1])).
% 7.85/1.51  
% 7.85/1.51  fof(f6,axiom,(
% 7.85/1.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f39,plain,(
% 7.85/1.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f6])).
% 7.85/1.51  
% 7.85/1.51  fof(f7,axiom,(
% 7.85/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f24,plain,(
% 7.85/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 7.85/1.51    inference(ennf_transformation,[],[f7])).
% 7.85/1.51  
% 7.85/1.51  fof(f40,plain,(
% 7.85/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 7.85/1.51    inference(cnf_transformation,[],[f24])).
% 7.85/1.51  
% 7.85/1.51  fof(f8,axiom,(
% 7.85/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f25,plain,(
% 7.85/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.85/1.51    inference(ennf_transformation,[],[f8])).
% 7.85/1.51  
% 7.85/1.51  fof(f41,plain,(
% 7.85/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f25])).
% 7.85/1.51  
% 7.85/1.51  fof(f18,axiom,(
% 7.85/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f26,plain,(
% 7.85/1.51    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 7.85/1.51    inference(ennf_transformation,[],[f18])).
% 7.85/1.51  
% 7.85/1.51  fof(f51,plain,(
% 7.85/1.51    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f26])).
% 7.85/1.51  
% 7.85/1.51  fof(f5,axiom,(
% 7.85/1.51    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f22,plain,(
% 7.85/1.51    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.85/1.51    inference(ennf_transformation,[],[f5])).
% 7.85/1.51  
% 7.85/1.51  fof(f23,plain,(
% 7.85/1.51    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.85/1.51    inference(flattening,[],[f22])).
% 7.85/1.51  
% 7.85/1.51  fof(f38,plain,(
% 7.85/1.51    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f23])).
% 7.85/1.51  
% 7.85/1.51  fof(f19,conjecture,(
% 7.85/1.51    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f20,negated_conjecture,(
% 7.85/1.51    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 7.85/1.51    inference(negated_conjecture,[],[f19])).
% 7.85/1.51  
% 7.85/1.51  fof(f27,plain,(
% 7.85/1.51    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 7.85/1.51    inference(ennf_transformation,[],[f20])).
% 7.85/1.51  
% 7.85/1.51  fof(f30,plain,(
% 7.85/1.51    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 7.85/1.51    introduced(choice_axiom,[])).
% 7.85/1.51  
% 7.85/1.51  fof(f31,plain,(
% 7.85/1.51    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 7.85/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f30])).
% 7.85/1.51  
% 7.85/1.51  fof(f52,plain,(
% 7.85/1.51    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 7.85/1.51    inference(cnf_transformation,[],[f31])).
% 7.85/1.51  
% 7.85/1.51  fof(f10,axiom,(
% 7.85/1.51    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f43,plain,(
% 7.85/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f10])).
% 7.85/1.51  
% 7.85/1.51  fof(f3,axiom,(
% 7.85/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f36,plain,(
% 7.85/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.85/1.51    inference(cnf_transformation,[],[f3])).
% 7.85/1.51  
% 7.85/1.51  fof(f53,plain,(
% 7.85/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.85/1.51    inference(definition_unfolding,[],[f43,f36])).
% 7.85/1.51  
% 7.85/1.51  fof(f62,plain,(
% 7.85/1.51    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 7.85/1.51    inference(definition_unfolding,[],[f52,f53,f53])).
% 7.85/1.51  
% 7.85/1.51  fof(f9,axiom,(
% 7.85/1.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f42,plain,(
% 7.85/1.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.85/1.51    inference(cnf_transformation,[],[f9])).
% 7.85/1.51  
% 7.85/1.51  fof(f60,plain,(
% 7.85/1.51    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 7.85/1.51    inference(definition_unfolding,[],[f42,f53])).
% 7.85/1.51  
% 7.85/1.51  fof(f4,axiom,(
% 7.85/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f21,plain,(
% 7.85/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.85/1.51    inference(ennf_transformation,[],[f4])).
% 7.85/1.51  
% 7.85/1.51  fof(f37,plain,(
% 7.85/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f21])).
% 7.85/1.51  
% 7.85/1.51  fof(f59,plain,(
% 7.85/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) | ~r1_tarski(X0,X1)) )),
% 7.85/1.51    inference(definition_unfolding,[],[f37,f53])).
% 7.85/1.51  
% 7.85/1.51  fof(f2,axiom,(
% 7.85/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f28,plain,(
% 7.85/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.85/1.51    inference(nnf_transformation,[],[f2])).
% 7.85/1.51  
% 7.85/1.51  fof(f29,plain,(
% 7.85/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.85/1.51    inference(flattening,[],[f28])).
% 7.85/1.51  
% 7.85/1.51  fof(f33,plain,(
% 7.85/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.85/1.51    inference(cnf_transformation,[],[f29])).
% 7.85/1.51  
% 7.85/1.51  fof(f64,plain,(
% 7.85/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.85/1.51    inference(equality_resolution,[],[f33])).
% 7.85/1.51  
% 7.85/1.51  cnf(c_162,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.85/1.51      theory(equality) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_0,plain,
% 7.85/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.85/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_1069,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
% 7.85/1.51      | r1_tarski(X3,k3_xboole_0(X2,X1))
% 7.85/1.51      | X3 != X0 ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_162,c_0]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_6,plain,
% 7.85/1.51      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.85/1.51      inference(cnf_transformation,[],[f39]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_4274,plain,
% 7.85/1.51      ( r1_tarski(X0,k3_xboole_0(X1,X2))
% 7.85/1.51      | X0 != k3_xboole_0(k3_xboole_0(X2,X1),X3) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_1069,c_6]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_8538,plain,
% 7.85/1.51      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X2,X1)) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_4274,c_0]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_7,plain,
% 7.85/1.51      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 7.85/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_8561,plain,
% 7.85/1.51      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X2) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_8538,c_7]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_160,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_159,plain,( X0 = X0 ),theory(equality) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_1054,plain,
% 7.85/1.51      ( X0 != X1 | X1 = X0 ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_160,c_159]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_8,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.85/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_2439,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1) | X0 = k3_xboole_0(X0,X1) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_1054,c_8]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_1077,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_162,c_159]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_3122,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1)
% 7.85/1.51      | r1_tarski(X0,X2)
% 7.85/1.51      | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_2439,c_1077]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_9312,plain,
% 7.85/1.51      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X2,X1)) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_8561,c_3122]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_1073,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1)
% 7.85/1.51      | ~ r1_tarski(X1,X2)
% 7.85/1.51      | r1_tarski(X3,k3_xboole_0(X1,X2))
% 7.85/1.51      | X3 != X0 ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_162,c_8]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_6567,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1)
% 7.85/1.51      | ~ r1_tarski(X1,X2)
% 7.85/1.51      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_1073,c_159]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_10928,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_9312,c_6567]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_11,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
% 7.85/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_13130,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1)
% 7.85/1.51      | ~ r1_tarski(X2,k1_zfmisc_1(X0))
% 7.85/1.51      | r1_tarski(X2,k1_zfmisc_1(X1)) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_10928,c_11]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_32723,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1)
% 7.85/1.51      | r1_tarski(k3_xboole_0(k1_zfmisc_1(X0),X2),k1_zfmisc_1(X1)) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_13130,c_6]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_5,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1)
% 7.85/1.51      | ~ r1_tarski(X2,X1)
% 7.85/1.51      | r1_tarski(k5_xboole_0(X0,X2),X1) ),
% 7.85/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_12,negated_conjecture,
% 7.85/1.51      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
% 7.85/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_858,plain,
% 7.85/1.51      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
% 7.85/1.51      | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_5,c_12]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_446,plain,
% 7.85/1.51      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
% 7.85/1.51      | r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
% 7.85/1.51      | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
% 7.85/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_485,plain,
% 7.85/1.51      ( r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
% 7.85/1.51      | ~ r1_tarski(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) ),
% 7.85/1.51      inference(instantiation,[status(thm)],[c_11]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_9,plain,
% 7.85/1.51      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 7.85/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_574,plain,
% 7.85/1.51      ( r1_tarski(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) ),
% 7.85/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_1084,plain,
% 7.85/1.51      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
% 7.85/1.51      inference(global_propositional_subsumption,
% 7.85/1.51                [status(thm)],
% 7.85/1.51                [c_858,c_12,c_446,c_485,c_574]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_1324,plain,
% 7.85/1.51      ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
% 7.85/1.51      | ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_1084,c_5]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_33998,plain,
% 7.85/1.51      ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
% 7.85/1.51      | ~ r1_tarski(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_32723,c_1324]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_2998,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))
% 7.85/1.51      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
% 7.85/1.51      inference(instantiation,[status(thm)],[c_11]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_6876,plain,
% 7.85/1.51      ( r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))
% 7.85/1.51      | ~ r1_tarski(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) ),
% 7.85/1.51      inference(instantiation,[status(thm)],[c_2998]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_34009,plain,
% 7.85/1.51      ( ~ r1_tarski(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))) ),
% 7.85/1.51      inference(global_propositional_subsumption,
% 7.85/1.51                [status(thm)],
% 7.85/1.51                [c_33998,c_6876]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_4,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1)
% 7.85/1.51      | r1_tarski(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
% 7.85/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_34021,plain,
% 7.85/1.51      ( ~ r1_tarski(sK1,sK1) ),
% 7.85/1.51      inference(resolution,[status(thm)],[c_34009,c_4]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_3,plain,
% 7.85/1.51      ( r1_tarski(X0,X0) ),
% 7.85/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_7331,plain,
% 7.85/1.51      ( r1_tarski(sK1,sK1) ),
% 7.85/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(contradiction,plain,
% 7.85/1.51      ( $false ),
% 7.85/1.51      inference(minisat,[status(thm)],[c_34021,c_7331]) ).
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.85/1.51  
% 7.85/1.51  ------                               Statistics
% 7.85/1.51  
% 7.85/1.51  ------ Selected
% 7.85/1.51  
% 7.85/1.51  total_time:                             0.81
% 7.85/1.51  
%------------------------------------------------------------------------------
