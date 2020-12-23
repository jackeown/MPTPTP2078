%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:24 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 167 expanded)
%              Number of clauses        :   36 (  40 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  146 ( 248 expanded)
%              Number of equality atoms :   82 ( 154 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f26])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f28])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f36,f49,f49,f33])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f48,f48])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f37,f33,f49])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_235,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_230,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_232,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1507,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_230,c_232])).

cnf(c_1913,plain,
    ( r2_hidden(sK0(sK2,X0),sK1) = iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_235,c_1507])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_236,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1918,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1913,c_236])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_234,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2001,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1918,c_234])).

cnf(c_5,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2003,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK2,sK2))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2001,c_5])).

cnf(c_7,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_9,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_233,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_233,c_8])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k2_enumset1(X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_231,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_633,plain,
    ( k3_tarski(k2_enumset1(sK2,sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_230,c_231])).

cnf(c_999,plain,
    ( k3_tarski(k2_enumset1(sK2,sK2,sK2,sK1)) = k4_subset_1(sK1,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_243,c_633])).

cnf(c_1237,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k4_subset_1(sK1,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_7,c_999])).

cnf(c_2004,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK2,sK2))) = k4_subset_1(sK1,sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2003,c_1237])).

cnf(c_3,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_648,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_6])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_657,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_648,c_2])).

cnf(c_2005,plain,
    ( k4_subset_1(sK1,sK2,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_2004,c_3,c_657])).

cnf(c_12,negated_conjecture,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_248,plain,
    ( k4_subset_1(sK1,sK2,sK1) != sK1 ),
    inference(demodulation,[status(thm)],[c_12,c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2005,c_248])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:09:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.52/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/0.98  
% 3.52/0.98  ------  iProver source info
% 3.52/0.98  
% 3.52/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.52/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/0.98  git: non_committed_changes: false
% 3.52/0.98  git: last_make_outside_of_git: false
% 3.52/0.98  
% 3.52/0.98  ------ 
% 3.52/0.98  ------ Parsing...
% 3.52/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/0.98  
% 3.52/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/0.98  ------ Proving...
% 3.52/0.98  ------ Problem Properties 
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  clauses                                 14
% 3.52/0.98  conjectures                             2
% 3.52/0.98  EPR                                     0
% 3.52/0.98  Horn                                    13
% 3.52/0.98  unary                                   9
% 3.52/0.98  binary                                  3
% 3.52/0.98  lits                                    21
% 3.52/0.98  lits eq                                 9
% 3.52/0.98  fd_pure                                 0
% 3.52/0.98  fd_pseudo                               0
% 3.52/0.98  fd_cond                                 0
% 3.52/0.98  fd_pseudo_cond                          0
% 3.52/0.98  AC symbols                              0
% 3.52/0.98  
% 3.52/0.98  ------ Input Options Time Limit: Unbounded
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  ------ 
% 3.52/0.98  Current options:
% 3.52/0.98  ------ 
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  ------ Proving...
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  % SZS status Theorem for theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  fof(f1,axiom,(
% 3.52/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f19,plain,(
% 3.52/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.52/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 3.52/0.98  
% 3.52/0.98  fof(f20,plain,(
% 3.52/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f19])).
% 3.52/0.98  
% 3.52/0.98  fof(f26,plain,(
% 3.52/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f27,plain,(
% 3.52/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f26])).
% 3.52/0.98  
% 3.52/0.98  fof(f30,plain,(
% 3.52/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f27])).
% 3.52/0.98  
% 3.52/0.98  fof(f16,conjecture,(
% 3.52/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f17,negated_conjecture,(
% 3.52/0.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 3.52/0.98    inference(negated_conjecture,[],[f16])).
% 3.52/0.98  
% 3.52/0.98  fof(f25,plain,(
% 3.52/0.98    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f17])).
% 3.52/0.98  
% 3.52/0.98  fof(f28,plain,(
% 3.52/0.98    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.52/0.98    introduced(choice_axiom,[])).
% 3.52/0.98  
% 3.52/0.98  fof(f29,plain,(
% 3.52/0.98    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.52/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f28])).
% 3.52/0.98  
% 3.52/0.98  fof(f46,plain,(
% 3.52/0.98    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.52/0.98    inference(cnf_transformation,[],[f29])).
% 3.52/0.98  
% 3.52/0.98  fof(f14,axiom,(
% 3.52/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f22,plain,(
% 3.52/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/0.98    inference(ennf_transformation,[],[f14])).
% 3.52/0.98  
% 3.52/0.98  fof(f44,plain,(
% 3.52/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f22])).
% 3.52/0.98  
% 3.52/0.98  fof(f31,plain,(
% 3.52/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f27])).
% 3.52/0.98  
% 3.52/0.98  fof(f5,axiom,(
% 3.52/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f21,plain,(
% 3.52/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.52/0.98    inference(ennf_transformation,[],[f5])).
% 3.52/0.98  
% 3.52/0.98  fof(f35,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f21])).
% 3.52/0.98  
% 3.52/0.98  fof(f6,axiom,(
% 3.52/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f36,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f6])).
% 3.52/0.98  
% 3.52/0.98  fof(f11,axiom,(
% 3.52/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f41,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f11])).
% 3.52/0.98  
% 3.52/0.98  fof(f9,axiom,(
% 3.52/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f39,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f9])).
% 3.52/0.98  
% 3.52/0.98  fof(f10,axiom,(
% 3.52/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f40,plain,(
% 3.52/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f10])).
% 3.52/0.98  
% 3.52/0.98  fof(f48,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.52/0.98    inference(definition_unfolding,[],[f39,f40])).
% 3.52/0.98  
% 3.52/0.98  fof(f49,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.52/0.98    inference(definition_unfolding,[],[f41,f48])).
% 3.52/0.98  
% 3.52/0.98  fof(f3,axiom,(
% 3.52/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f33,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f3])).
% 3.52/0.98  
% 3.52/0.98  fof(f51,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.52/0.98    inference(definition_unfolding,[],[f36,f49,f49,f33])).
% 3.52/0.98  
% 3.52/0.98  fof(f8,axiom,(
% 3.52/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f38,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.52/0.98    inference(cnf_transformation,[],[f8])).
% 3.52/0.98  
% 3.52/0.98  fof(f53,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.52/0.98    inference(definition_unfolding,[],[f38,f48,f48])).
% 3.52/0.98  
% 3.52/0.98  fof(f13,axiom,(
% 3.52/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f43,plain,(
% 3.52/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f13])).
% 3.52/0.98  
% 3.52/0.98  fof(f12,axiom,(
% 3.52/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f42,plain,(
% 3.52/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.52/0.98    inference(cnf_transformation,[],[f12])).
% 3.52/0.98  
% 3.52/0.98  fof(f15,axiom,(
% 3.52/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f23,plain,(
% 3.52/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.52/0.98    inference(ennf_transformation,[],[f15])).
% 3.52/0.98  
% 3.52/0.98  fof(f24,plain,(
% 3.52/0.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.52/0.98    inference(flattening,[],[f23])).
% 3.52/0.98  
% 3.52/0.98  fof(f45,plain,(
% 3.52/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.52/0.98    inference(cnf_transformation,[],[f24])).
% 3.52/0.98  
% 3.52/0.98  fof(f54,plain,(
% 3.52/0.98    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.52/0.98    inference(definition_unfolding,[],[f45,f49])).
% 3.52/0.98  
% 3.52/0.98  fof(f4,axiom,(
% 3.52/0.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f34,plain,(
% 3.52/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.52/0.98    inference(cnf_transformation,[],[f4])).
% 3.52/0.98  
% 3.52/0.98  fof(f50,plain,(
% 3.52/0.98    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.52/0.98    inference(definition_unfolding,[],[f34,f49])).
% 3.52/0.98  
% 3.52/0.98  fof(f7,axiom,(
% 3.52/0.98    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f37,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 3.52/0.98    inference(cnf_transformation,[],[f7])).
% 3.52/0.98  
% 3.52/0.98  fof(f52,plain,(
% 3.52/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0) )),
% 3.52/0.98    inference(definition_unfolding,[],[f37,f33,f49])).
% 3.52/0.98  
% 3.52/0.98  fof(f2,axiom,(
% 3.52/0.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.52/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.98  
% 3.52/0.98  fof(f18,plain,(
% 3.52/0.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.52/0.98    inference(rectify,[],[f2])).
% 3.52/0.98  
% 3.52/0.98  fof(f32,plain,(
% 3.52/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.52/0.98    inference(cnf_transformation,[],[f18])).
% 3.52/0.98  
% 3.52/0.98  fof(f47,plain,(
% 3.52/0.98    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))),
% 3.52/0.98    inference(cnf_transformation,[],[f29])).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1,plain,
% 3.52/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_235,plain,
% 3.52/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.52/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_13,negated_conjecture,
% 3.52/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.52/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_230,plain,
% 3.52/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_10,plain,
% 3.52/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/0.98      | ~ r2_hidden(X2,X0)
% 3.52/0.98      | r2_hidden(X2,X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_232,plain,
% 3.52/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.52/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.52/0.98      | r2_hidden(X2,X1) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1507,plain,
% 3.52/0.98      ( r2_hidden(X0,sK2) != iProver_top
% 3.52/0.98      | r2_hidden(X0,sK1) = iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_230,c_232]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1913,plain,
% 3.52/0.98      ( r2_hidden(sK0(sK2,X0),sK1) = iProver_top
% 3.52/0.98      | r1_tarski(sK2,X0) = iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_235,c_1507]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_0,plain,
% 3.52/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.52/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_236,plain,
% 3.52/0.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.52/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1918,plain,
% 3.52/0.98      ( r1_tarski(sK2,sK1) = iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_1913,c_236]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_4,plain,
% 3.52/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.52/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_234,plain,
% 3.52/0.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2001,plain,
% 3.52/0.98      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_1918,c_234]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_5,plain,
% 3.52/0.98      ( k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 3.52/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2003,plain,
% 3.52/0.98      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK2,sK2))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_2001,c_5]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_7,plain,
% 3.52/0.98      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 3.52/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_9,plain,
% 3.52/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.52/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_233,plain,
% 3.52/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_8,plain,
% 3.52/0.98      ( k2_subset_1(X0) = X0 ),
% 3.52/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_243,plain,
% 3.52/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.52/0.98      inference(light_normalisation,[status(thm)],[c_233,c_8]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_11,plain,
% 3.52/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.52/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.52/0.98      | k3_tarski(k2_enumset1(X0,X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 3.52/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_231,plain,
% 3.52/0.98      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.52/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.52/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.52/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_633,plain,
% 3.52/0.98      ( k3_tarski(k2_enumset1(sK2,sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
% 3.52/0.98      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_230,c_231]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_999,plain,
% 3.52/0.98      ( k3_tarski(k2_enumset1(sK2,sK2,sK2,sK1)) = k4_subset_1(sK1,sK2,sK1) ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_243,c_633]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_1237,plain,
% 3.52/0.98      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k4_subset_1(sK1,sK2,sK1) ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_7,c_999]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2004,plain,
% 3.52/0.98      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK2,sK2))) = k4_subset_1(sK1,sK2,sK1) ),
% 3.52/0.98      inference(light_normalisation,[status(thm)],[c_2003,c_1237]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_3,plain,
% 3.52/0.98      ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.52/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_6,plain,
% 3.52/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0 ),
% 3.52/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_648,plain,
% 3.52/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 3.52/0.98      inference(superposition,[status(thm)],[c_3,c_6]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2,plain,
% 3.52/0.98      ( k3_xboole_0(X0,X0) = X0 ),
% 3.52/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_657,plain,
% 3.52/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.52/0.98      inference(light_normalisation,[status(thm)],[c_648,c_2]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_2005,plain,
% 3.52/0.98      ( k4_subset_1(sK1,sK2,sK1) = sK1 ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_2004,c_3,c_657]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_12,negated_conjecture,
% 3.52/0.98      ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
% 3.52/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(c_248,plain,
% 3.52/0.98      ( k4_subset_1(sK1,sK2,sK1) != sK1 ),
% 3.52/0.98      inference(demodulation,[status(thm)],[c_12,c_8]) ).
% 3.52/0.98  
% 3.52/0.98  cnf(contradiction,plain,
% 3.52/0.98      ( $false ),
% 3.52/0.98      inference(minisat,[status(thm)],[c_2005,c_248]) ).
% 3.52/0.98  
% 3.52/0.98  
% 3.52/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/0.98  
% 3.52/0.98  ------                               Statistics
% 3.52/0.98  
% 3.52/0.98  ------ Selected
% 3.52/0.98  
% 3.52/0.98  total_time:                             0.098
% 3.52/0.98  
%------------------------------------------------------------------------------
