%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:17 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 218 expanded)
%              Number of clauses        :   34 (  78 expanded)
%              Number of leaves         :    9 (  52 expanded)
%              Depth                    :   18
%              Number of atoms          :  134 ( 420 expanded)
%              Number of equality atoms :   71 ( 197 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
        & ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) ) )
   => ( ~ r1_xboole_0(k2_zfmisc_1(sK1,sK3),k2_zfmisc_1(sK2,sK4))
      & ( r1_xboole_0(sK3,sK4)
        | r1_xboole_0(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK1,sK3),k2_zfmisc_1(sK2,sK4))
    & ( r1_xboole_0(sK3,sK4)
      | r1_xboole_0(sK1,sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f18])).

fof(f31,plain,
    ( r1_xboole_0(sK3,sK4)
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(definition_unfolding,[],[f30,f23,f23,f23])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f13])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f32,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK1,sK3),k2_zfmisc_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f28])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK3,sK4)
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2306,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2308,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2394,plain,
    ( k4_xboole_0(sK3,sK4) = sK3
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2306,c_2308])).

cnf(c_2405,plain,
    ( k4_xboole_0(sK3,sK4) = sK3
    | k4_xboole_0(sK1,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_2394,c_2308])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2439,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK3),k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK4))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(sK3,sK3))
    | k4_xboole_0(sK1,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_2405,c_9])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_2310,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2393,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_2310,c_2308])).

cnf(c_2698,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k1_xboole_0))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_2393,c_9])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2700,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X2)) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_2698,c_6,c_2393])).

cnf(c_3564,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK3),k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK4))) = k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X0,sK3))
    | k4_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2439,c_2700])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2311,plain,
    ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3576,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | r2_hidden(sK0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK4)),k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X0,sK3))) = iProver_top
    | r1_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3564,c_2311])).

cnf(c_0,negated_conjecture,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2312,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2697,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
    | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2393,c_2312])).

cnf(c_2997,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2697,c_2310])).

cnf(c_5559,plain,
    ( k4_xboole_0(sK1,sK2) = sK1
    | r1_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK4)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3576,c_2997])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(sK1,sK3),k2_zfmisc_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2307,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK1,sK3),k2_zfmisc_1(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5566,plain,
    ( k4_xboole_0(sK1,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_5559,c_2307])).

cnf(c_5586,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK1,X0),k4_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X1))) = k2_zfmisc_1(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5566,c_9])).

cnf(c_2694,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_xboole_0,X2))) = k2_zfmisc_1(k4_xboole_0(X0,X0),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_2393,c_9])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2721,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,X0),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_2694,c_7,c_2393])).

cnf(c_5597,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK1,X0),k4_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X1))) = k4_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_5586,c_2721])).

cnf(c_5745,plain,
    ( r2_hidden(sK0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X1)),k4_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5597,c_2311])).

cnf(c_6486,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5745,c_2997])).

cnf(c_6493,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_6486,c_2307])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:45:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.46/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/0.99  
% 3.46/0.99  ------  iProver source info
% 3.46/0.99  
% 3.46/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.46/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/0.99  git: non_committed_changes: false
% 3.46/0.99  git: last_make_outside_of_git: false
% 3.46/0.99  
% 3.46/0.99  ------ 
% 3.46/0.99  ------ Parsing...
% 3.46/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  ------ Proving...
% 3.46/0.99  ------ Problem Properties 
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  clauses                                 12
% 3.46/0.99  conjectures                             3
% 3.46/0.99  EPR                                     2
% 3.46/0.99  Horn                                    9
% 3.46/0.99  unary                                   6
% 3.46/0.99  binary                                  5
% 3.46/0.99  lits                                    19
% 3.46/0.99  lits eq                                 9
% 3.46/0.99  fd_pure                                 0
% 3.46/0.99  fd_pseudo                               0
% 3.46/0.99  fd_cond                                 1
% 3.46/0.99  fd_pseudo_cond                          0
% 3.46/0.99  AC symbols                              0
% 3.46/0.99  
% 3.46/0.99  ------ Input Options Time Limit: Unbounded
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing...
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.46/0.99  Current options:
% 3.46/0.99  ------ 
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.46/0.99  
% 3.46/0.99  ------ Proving...
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  % SZS status Theorem for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99   Resolution empty clause
% 3.46/0.99  
% 3.46/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  fof(f8,conjecture,(
% 3.46/0.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f9,negated_conjecture,(
% 3.46/0.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 3.46/0.99    inference(negated_conjecture,[],[f8])).
% 3.46/0.99  
% 3.46/0.99  fof(f12,plain,(
% 3.46/0.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)))),
% 3.46/0.99    inference(ennf_transformation,[],[f9])).
% 3.46/0.99  
% 3.46/0.99  fof(f18,plain,(
% 3.46/0.99    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1))) => (~r1_xboole_0(k2_zfmisc_1(sK1,sK3),k2_zfmisc_1(sK2,sK4)) & (r1_xboole_0(sK3,sK4) | r1_xboole_0(sK1,sK2)))),
% 3.46/0.99    introduced(choice_axiom,[])).
% 3.46/0.99  
% 3.46/0.99  fof(f19,plain,(
% 3.46/0.99    ~r1_xboole_0(k2_zfmisc_1(sK1,sK3),k2_zfmisc_1(sK2,sK4)) & (r1_xboole_0(sK3,sK4) | r1_xboole_0(sK1,sK2))),
% 3.46/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f18])).
% 3.46/0.99  
% 3.46/0.99  fof(f31,plain,(
% 3.46/0.99    r1_xboole_0(sK3,sK4) | r1_xboole_0(sK1,sK2)),
% 3.46/0.99    inference(cnf_transformation,[],[f19])).
% 3.46/0.99  
% 3.46/0.99  fof(f5,axiom,(
% 3.46/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f15,plain,(
% 3.46/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.46/0.99    inference(nnf_transformation,[],[f5])).
% 3.46/0.99  
% 3.46/0.99  fof(f25,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f15])).
% 3.46/0.99  
% 3.46/0.99  fof(f7,axiom,(
% 3.46/0.99    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f30,plain,(
% 3.46/0.99    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f7])).
% 3.46/0.99  
% 3.46/0.99  fof(f3,axiom,(
% 3.46/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f23,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f3])).
% 3.46/0.99  
% 3.46/0.99  fof(f36,plain,(
% 3.46/0.99    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 3.46/0.99    inference(definition_unfolding,[],[f30,f23,f23,f23])).
% 3.46/0.99  
% 3.46/0.99  fof(f4,axiom,(
% 3.46/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f24,plain,(
% 3.46/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f4])).
% 3.46/0.99  
% 3.46/0.99  fof(f6,axiom,(
% 3.46/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f16,plain,(
% 3.46/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.46/0.99    inference(nnf_transformation,[],[f6])).
% 3.46/0.99  
% 3.46/0.99  fof(f17,plain,(
% 3.46/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.46/0.99    inference(flattening,[],[f16])).
% 3.46/0.99  
% 3.46/0.99  fof(f29,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.46/0.99    inference(cnf_transformation,[],[f17])).
% 3.46/0.99  
% 3.46/0.99  fof(f37,plain,(
% 3.46/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.46/0.99    inference(equality_resolution,[],[f29])).
% 3.46/0.99  
% 3.46/0.99  fof(f1,axiom,(
% 3.46/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.99  
% 3.46/0.99  fof(f10,plain,(
% 3.46/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.46/0.99    inference(rectify,[],[f1])).
% 3.46/0.99  
% 3.46/0.99  fof(f11,plain,(
% 3.46/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.46/0.99    inference(ennf_transformation,[],[f10])).
% 3.46/0.99  
% 3.46/0.99  fof(f13,plain,(
% 3.46/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.46/0.99    introduced(choice_axiom,[])).
% 3.46/0.99  
% 3.46/0.99  fof(f14,plain,(
% 3.46/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.46/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f13])).
% 3.46/0.99  
% 3.46/0.99  fof(f20,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.46/0.99    inference(cnf_transformation,[],[f14])).
% 3.46/0.99  
% 3.46/0.99  fof(f34,plain,(
% 3.46/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 3.46/0.99    inference(definition_unfolding,[],[f20,f23])).
% 3.46/0.99  
% 3.46/0.99  fof(f21,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.46/0.99    inference(cnf_transformation,[],[f14])).
% 3.46/0.99  
% 3.46/0.99  fof(f33,plain,(
% 3.46/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.46/0.99    inference(definition_unfolding,[],[f21,f23])).
% 3.46/0.99  
% 3.46/0.99  fof(f32,plain,(
% 3.46/0.99    ~r1_xboole_0(k2_zfmisc_1(sK1,sK3),k2_zfmisc_1(sK2,sK4))),
% 3.46/0.99    inference(cnf_transformation,[],[f19])).
% 3.46/0.99  
% 3.46/0.99  fof(f28,plain,(
% 3.46/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.46/0.99    inference(cnf_transformation,[],[f17])).
% 3.46/0.99  
% 3.46/0.99  fof(f38,plain,(
% 3.46/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.46/0.99    inference(equality_resolution,[],[f28])).
% 3.46/0.99  
% 3.46/0.99  cnf(c_11,negated_conjecture,
% 3.46/0.99      ( r1_xboole_0(sK3,sK4) | r1_xboole_0(sK1,sK2) ),
% 3.46/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2306,plain,
% 3.46/0.99      ( r1_xboole_0(sK3,sK4) = iProver_top
% 3.46/0.99      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_5,plain,
% 3.46/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2308,plain,
% 3.46/0.99      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2394,plain,
% 3.46/0.99      ( k4_xboole_0(sK3,sK4) = sK3 | r1_xboole_0(sK1,sK2) = iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2306,c_2308]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2405,plain,
% 3.46/0.99      ( k4_xboole_0(sK3,sK4) = sK3 | k4_xboole_0(sK1,sK2) = sK1 ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2394,c_2308]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_9,plain,
% 3.46/0.99      ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
% 3.46/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2439,plain,
% 3.46/0.99      ( k4_xboole_0(k2_zfmisc_1(X0,sK3),k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK4))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(sK3,sK3))
% 3.46/0.99      | k4_xboole_0(sK1,sK2) = sK1 ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2405,c_9]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3,plain,
% 3.46/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.46/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2310,plain,
% 3.46/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2393,plain,
% 3.46/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2310,c_2308]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2698,plain,
% 3.46/0.99      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k1_xboole_0))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X1,X1)) ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2393,c_9]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6,plain,
% 3.46/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2700,plain,
% 3.46/0.99      ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X2)) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2)) ),
% 3.46/0.99      inference(demodulation,[status(thm)],[c_2698,c_6,c_2393]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3564,plain,
% 3.46/0.99      ( k4_xboole_0(k2_zfmisc_1(X0,sK3),k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK4))) = k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X0,sK3))
% 3.46/0.99      | k4_xboole_0(sK1,sK2) = sK1 ),
% 3.46/0.99      inference(demodulation,[status(thm)],[c_2439,c_2700]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_1,plain,
% 3.46/0.99      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 3.46/0.99      | r1_xboole_0(X0,X1) ),
% 3.46/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2311,plain,
% 3.46/0.99      ( r2_hidden(sK0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top
% 3.46/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_3576,plain,
% 3.46/0.99      ( k4_xboole_0(sK1,sK2) = sK1
% 3.46/0.99      | r2_hidden(sK0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK4)),k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X0,sK3))) = iProver_top
% 3.46/0.99      | r1_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK4)) = iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_3564,c_2311]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_0,negated_conjecture,
% 3.46/0.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.46/0.99      | ~ r1_xboole_0(X1,X2) ),
% 3.46/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2312,plain,
% 3.46/0.99      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 3.46/0.99      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2697,plain,
% 3.46/0.99      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top
% 3.46/0.99      | r1_xboole_0(X1,k1_xboole_0) != iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2393,c_2312]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2997,plain,
% 3.46/0.99      ( r2_hidden(X0,k4_xboole_0(X1,X1)) != iProver_top ),
% 3.46/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2697,c_2310]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_5559,plain,
% 3.46/0.99      ( k4_xboole_0(sK1,sK2) = sK1
% 3.46/0.99      | r1_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,sK4)) = iProver_top ),
% 3.46/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3576,c_2997]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_10,negated_conjecture,
% 3.46/0.99      ( ~ r1_xboole_0(k2_zfmisc_1(sK1,sK3),k2_zfmisc_1(sK2,sK4)) ),
% 3.46/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2307,plain,
% 3.46/0.99      ( r1_xboole_0(k2_zfmisc_1(sK1,sK3),k2_zfmisc_1(sK2,sK4)) != iProver_top ),
% 3.46/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_5566,plain,
% 3.46/0.99      ( k4_xboole_0(sK1,sK2) = sK1 ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_5559,c_2307]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_5586,plain,
% 3.46/0.99      ( k4_xboole_0(k2_zfmisc_1(sK1,X0),k4_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X1))) = k2_zfmisc_1(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_5566,c_9]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2694,plain,
% 3.46/0.99      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_xboole_0,X2))) = k2_zfmisc_1(k4_xboole_0(X0,X0),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_2393,c_9]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_7,plain,
% 3.46/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.46/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_2721,plain,
% 3.46/0.99      ( k2_zfmisc_1(k4_xboole_0(X0,X0),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)) ),
% 3.46/0.99      inference(demodulation,[status(thm)],[c_2694,c_7,c_2393]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_5597,plain,
% 3.46/0.99      ( k4_xboole_0(k2_zfmisc_1(sK1,X0),k4_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X1))) = k4_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK1,X0)) ),
% 3.46/0.99      inference(demodulation,[status(thm)],[c_5586,c_2721]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_5745,plain,
% 3.46/0.99      ( r2_hidden(sK0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X1)),k4_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.46/0.99      | r1_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X1)) = iProver_top ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_5597,c_2311]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6486,plain,
% 3.46/0.99      ( r1_xboole_0(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK2,X1)) = iProver_top ),
% 3.46/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5745,c_2997]) ).
% 3.46/0.99  
% 3.46/0.99  cnf(c_6493,plain,
% 3.46/0.99      ( $false ),
% 3.46/0.99      inference(superposition,[status(thm)],[c_6486,c_2307]) ).
% 3.46/0.99  
% 3.46/0.99  
% 3.46/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.46/0.99  
% 3.46/0.99  ------                               Statistics
% 3.46/0.99  
% 3.46/0.99  ------ Selected
% 3.46/0.99  
% 3.46/0.99  total_time:                             0.188
% 3.46/0.99  
%------------------------------------------------------------------------------
