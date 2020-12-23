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
% DateTime   : Thu Dec  3 11:37:53 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 167 expanded)
%              Number of clauses        :   39 (  54 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   21
%              Number of atoms          :  202 ( 570 expanded)
%              Number of equality atoms :   96 ( 166 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f15])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK3,sK5)
        | ~ r1_tarski(sK2,sK4) )
      & k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
      & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ~ r1_tarski(sK3,sK5)
      | ~ r1_tarski(sK2,sK4) )
    & k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
    & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f10,f21])).

fof(f33,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,
    ( ~ r1_tarski(sK3,sK5)
    | ~ r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_291,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_289,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_284,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_288,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_290,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_874,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
    | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_288,c_290])).

cnf(c_1166,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_284,c_874])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_287,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1206,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_287])).

cnf(c_1860,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_289,c_1206])).

cnf(c_3440,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK3,X0),sK5) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_291,c_1860])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_292,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8601,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3440,c_292])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_286,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1207,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_286])).

cnf(c_1997,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK0(sK2,X1),sK4) = iProver_top
    | r1_tarski(sK2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_291,c_1207])).

cnf(c_9719,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK2,X0),sK4) = iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_289,c_1997])).

cnf(c_10154,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_9719,c_292])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK2,sK4)
    | ~ r1_tarski(sK3,sK5) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_285,plain,
    ( r1_tarski(sK2,sK4) != iProver_top
    | r1_tarski(sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_10288,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_10154,c_285])).

cnf(c_10293,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8601,c_10288])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10349,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10293,c_11])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10352,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10349,c_8])).

cnf(c_10353,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_10352])).

cnf(c_10397,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10353,c_11])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_10399,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10397,c_7])).

cnf(c_10400,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10399])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : iproveropt_run.sh %d %s
% 0.09/0.29  % Computer   : n019.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.29  % CPULimit   : 60
% 0.13/0.29  % WCLimit    : 600
% 0.13/0.29  % DateTime   : Tue Dec  1 11:14:37 EST 2020
% 0.13/0.29  % CPUTime    : 
% 0.13/0.29  % Running in FOF mode
% 2.13/0.95  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/0.95  
% 2.13/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.13/0.95  
% 2.13/0.95  ------  iProver source info
% 2.13/0.95  
% 2.13/0.95  git: date: 2020-06-30 10:37:57 +0100
% 2.13/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.13/0.95  git: non_committed_changes: false
% 2.13/0.95  git: last_make_outside_of_git: false
% 2.13/0.95  
% 2.13/0.95  ------ 
% 2.13/0.95  
% 2.13/0.95  ------ Input Options
% 2.13/0.95  
% 2.13/0.95  --out_options                           all
% 2.13/0.95  --tptp_safe_out                         true
% 2.13/0.95  --problem_path                          ""
% 2.13/0.95  --include_path                          ""
% 2.13/0.95  --clausifier                            res/vclausify_rel
% 2.13/0.95  --clausifier_options                    --mode clausify
% 2.13/0.95  --stdin                                 false
% 2.13/0.95  --stats_out                             all
% 2.13/0.95  
% 2.13/0.95  ------ General Options
% 2.13/0.95  
% 2.13/0.95  --fof                                   false
% 2.13/0.95  --time_out_real                         305.
% 2.13/0.95  --time_out_virtual                      -1.
% 2.13/0.95  --symbol_type_check                     false
% 2.13/0.95  --clausify_out                          false
% 2.13/0.95  --sig_cnt_out                           false
% 2.13/0.95  --trig_cnt_out                          false
% 2.13/0.95  --trig_cnt_out_tolerance                1.
% 2.13/0.95  --trig_cnt_out_sk_spl                   false
% 2.13/0.95  --abstr_cl_out                          false
% 2.13/0.95  
% 2.13/0.95  ------ Global Options
% 2.13/0.95  
% 2.13/0.95  --schedule                              default
% 2.13/0.95  --add_important_lit                     false
% 2.13/0.95  --prop_solver_per_cl                    1000
% 2.13/0.95  --min_unsat_core                        false
% 2.13/0.95  --soft_assumptions                      false
% 2.13/0.95  --soft_lemma_size                       3
% 2.13/0.95  --prop_impl_unit_size                   0
% 2.13/0.95  --prop_impl_unit                        []
% 2.13/0.95  --share_sel_clauses                     true
% 2.13/0.95  --reset_solvers                         false
% 2.13/0.95  --bc_imp_inh                            [conj_cone]
% 2.13/0.95  --conj_cone_tolerance                   3.
% 2.13/0.95  --extra_neg_conj                        none
% 2.13/0.95  --large_theory_mode                     true
% 2.13/0.95  --prolific_symb_bound                   200
% 2.13/0.95  --lt_threshold                          2000
% 2.13/0.95  --clause_weak_htbl                      true
% 2.13/0.95  --gc_record_bc_elim                     false
% 2.13/0.95  
% 2.13/0.95  ------ Preprocessing Options
% 2.13/0.95  
% 2.13/0.95  --preprocessing_flag                    true
% 2.13/0.95  --time_out_prep_mult                    0.1
% 2.13/0.95  --splitting_mode                        input
% 2.13/0.95  --splitting_grd                         true
% 2.13/0.95  --splitting_cvd                         false
% 2.13/0.95  --splitting_cvd_svl                     false
% 2.13/0.95  --splitting_nvd                         32
% 2.13/0.95  --sub_typing                            true
% 2.13/0.95  --prep_gs_sim                           true
% 2.13/0.95  --prep_unflatten                        true
% 2.13/0.95  --prep_res_sim                          true
% 2.13/0.95  --prep_upred                            true
% 2.13/0.95  --prep_sem_filter                       exhaustive
% 2.13/0.95  --prep_sem_filter_out                   false
% 2.13/0.95  --pred_elim                             true
% 2.13/0.95  --res_sim_input                         true
% 2.13/0.95  --eq_ax_congr_red                       true
% 2.13/0.95  --pure_diseq_elim                       true
% 2.13/0.95  --brand_transform                       false
% 2.13/0.95  --non_eq_to_eq                          false
% 2.13/0.95  --prep_def_merge                        true
% 2.13/0.95  --prep_def_merge_prop_impl              false
% 2.13/0.95  --prep_def_merge_mbd                    true
% 2.13/0.95  --prep_def_merge_tr_red                 false
% 2.13/0.95  --prep_def_merge_tr_cl                  false
% 2.13/0.95  --smt_preprocessing                     true
% 2.13/0.95  --smt_ac_axioms                         fast
% 2.13/0.95  --preprocessed_out                      false
% 2.13/0.95  --preprocessed_stats                    false
% 2.13/0.95  
% 2.13/0.95  ------ Abstraction refinement Options
% 2.13/0.95  
% 2.13/0.95  --abstr_ref                             []
% 2.13/0.95  --abstr_ref_prep                        false
% 2.13/0.95  --abstr_ref_until_sat                   false
% 2.13/0.95  --abstr_ref_sig_restrict                funpre
% 2.13/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.95  --abstr_ref_under                       []
% 2.13/0.95  
% 2.13/0.95  ------ SAT Options
% 2.13/0.95  
% 2.13/0.95  --sat_mode                              false
% 2.13/0.95  --sat_fm_restart_options                ""
% 2.13/0.95  --sat_gr_def                            false
% 2.13/0.95  --sat_epr_types                         true
% 2.13/0.95  --sat_non_cyclic_types                  false
% 2.13/0.95  --sat_finite_models                     false
% 2.13/0.95  --sat_fm_lemmas                         false
% 2.13/0.95  --sat_fm_prep                           false
% 2.13/0.95  --sat_fm_uc_incr                        true
% 2.13/0.95  --sat_out_model                         small
% 2.13/0.95  --sat_out_clauses                       false
% 2.13/0.95  
% 2.13/0.95  ------ QBF Options
% 2.13/0.95  
% 2.13/0.95  --qbf_mode                              false
% 2.13/0.95  --qbf_elim_univ                         false
% 2.13/0.95  --qbf_dom_inst                          none
% 2.13/0.95  --qbf_dom_pre_inst                      false
% 2.13/0.95  --qbf_sk_in                             false
% 2.13/0.95  --qbf_pred_elim                         true
% 2.13/0.95  --qbf_split                             512
% 2.13/0.95  
% 2.13/0.95  ------ BMC1 Options
% 2.13/0.95  
% 2.13/0.95  --bmc1_incremental                      false
% 2.13/0.95  --bmc1_axioms                           reachable_all
% 2.13/0.95  --bmc1_min_bound                        0
% 2.13/0.95  --bmc1_max_bound                        -1
% 2.13/0.95  --bmc1_max_bound_default                -1
% 2.13/0.95  --bmc1_symbol_reachability              true
% 2.13/0.95  --bmc1_property_lemmas                  false
% 2.13/0.95  --bmc1_k_induction                      false
% 2.13/0.95  --bmc1_non_equiv_states                 false
% 2.13/0.95  --bmc1_deadlock                         false
% 2.13/0.95  --bmc1_ucm                              false
% 2.13/0.95  --bmc1_add_unsat_core                   none
% 2.13/0.95  --bmc1_unsat_core_children              false
% 2.13/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/0.95  --bmc1_out_stat                         full
% 2.13/0.95  --bmc1_ground_init                      false
% 2.13/0.95  --bmc1_pre_inst_next_state              false
% 2.13/0.95  --bmc1_pre_inst_state                   false
% 2.13/0.95  --bmc1_pre_inst_reach_state             false
% 2.13/0.95  --bmc1_out_unsat_core                   false
% 2.13/0.95  --bmc1_aig_witness_out                  false
% 2.13/0.95  --bmc1_verbose                          false
% 2.13/0.95  --bmc1_dump_clauses_tptp                false
% 2.13/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.13/0.95  --bmc1_dump_file                        -
% 2.13/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.13/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.13/0.95  --bmc1_ucm_extend_mode                  1
% 2.13/0.95  --bmc1_ucm_init_mode                    2
% 2.13/0.95  --bmc1_ucm_cone_mode                    none
% 2.13/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.13/0.95  --bmc1_ucm_relax_model                  4
% 2.13/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.13/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/0.95  --bmc1_ucm_layered_model                none
% 2.13/0.95  --bmc1_ucm_max_lemma_size               10
% 2.13/0.95  
% 2.13/0.95  ------ AIG Options
% 2.13/0.95  
% 2.13/0.95  --aig_mode                              false
% 2.13/0.95  
% 2.13/0.95  ------ Instantiation Options
% 2.13/0.95  
% 2.13/0.95  --instantiation_flag                    true
% 2.13/0.95  --inst_sos_flag                         false
% 2.13/0.95  --inst_sos_phase                        true
% 2.13/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/0.95  --inst_lit_sel_side                     num_symb
% 2.13/0.95  --inst_solver_per_active                1400
% 2.13/0.95  --inst_solver_calls_frac                1.
% 2.13/0.95  --inst_passive_queue_type               priority_queues
% 2.13/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/0.95  --inst_passive_queues_freq              [25;2]
% 2.13/0.95  --inst_dismatching                      true
% 2.13/0.95  --inst_eager_unprocessed_to_passive     true
% 2.13/0.95  --inst_prop_sim_given                   true
% 2.13/0.95  --inst_prop_sim_new                     false
% 2.13/0.95  --inst_subs_new                         false
% 2.13/0.95  --inst_eq_res_simp                      false
% 2.13/0.95  --inst_subs_given                       false
% 2.13/0.95  --inst_orphan_elimination               true
% 2.13/0.95  --inst_learning_loop_flag               true
% 2.13/0.95  --inst_learning_start                   3000
% 2.13/0.95  --inst_learning_factor                  2
% 2.13/0.95  --inst_start_prop_sim_after_learn       3
% 2.13/0.95  --inst_sel_renew                        solver
% 2.13/0.95  --inst_lit_activity_flag                true
% 2.13/0.95  --inst_restr_to_given                   false
% 2.13/0.95  --inst_activity_threshold               500
% 2.13/0.95  --inst_out_proof                        true
% 2.13/0.95  
% 2.13/0.95  ------ Resolution Options
% 2.13/0.95  
% 2.13/0.95  --resolution_flag                       true
% 2.13/0.95  --res_lit_sel                           adaptive
% 2.13/0.95  --res_lit_sel_side                      none
% 2.13/0.95  --res_ordering                          kbo
% 2.13/0.95  --res_to_prop_solver                    active
% 2.13/0.95  --res_prop_simpl_new                    false
% 2.13/0.95  --res_prop_simpl_given                  true
% 2.13/0.95  --res_passive_queue_type                priority_queues
% 2.13/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/0.95  --res_passive_queues_freq               [15;5]
% 2.13/0.95  --res_forward_subs                      full
% 2.13/0.95  --res_backward_subs                     full
% 2.13/0.95  --res_forward_subs_resolution           true
% 2.13/0.95  --res_backward_subs_resolution          true
% 2.13/0.95  --res_orphan_elimination                true
% 2.13/0.95  --res_time_limit                        2.
% 2.13/0.95  --res_out_proof                         true
% 2.13/0.95  
% 2.13/0.95  ------ Superposition Options
% 2.13/0.95  
% 2.13/0.95  --superposition_flag                    true
% 2.13/0.95  --sup_passive_queue_type                priority_queues
% 2.13/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.13/0.95  --demod_completeness_check              fast
% 2.13/0.95  --demod_use_ground                      true
% 2.13/0.95  --sup_to_prop_solver                    passive
% 2.13/0.95  --sup_prop_simpl_new                    true
% 2.13/0.95  --sup_prop_simpl_given                  true
% 2.13/0.95  --sup_fun_splitting                     false
% 2.13/0.95  --sup_smt_interval                      50000
% 2.13/0.95  
% 2.13/0.95  ------ Superposition Simplification Setup
% 2.13/0.95  
% 2.13/0.95  --sup_indices_passive                   []
% 2.13/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.95  --sup_full_bw                           [BwDemod]
% 2.13/0.95  --sup_immed_triv                        [TrivRules]
% 2.13/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.95  --sup_immed_bw_main                     []
% 2.13/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.95  
% 2.13/0.95  ------ Combination Options
% 2.13/0.95  
% 2.13/0.95  --comb_res_mult                         3
% 2.13/0.95  --comb_sup_mult                         2
% 2.13/0.95  --comb_inst_mult                        10
% 2.13/0.95  
% 2.13/0.95  ------ Debug Options
% 2.13/0.95  
% 2.13/0.95  --dbg_backtrace                         false
% 2.13/0.95  --dbg_dump_prop_clauses                 false
% 2.13/0.95  --dbg_dump_prop_clauses_file            -
% 2.13/0.95  --dbg_out_stat                          false
% 2.13/0.95  ------ Parsing...
% 2.13/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.13/0.95  
% 2.13/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.13/0.95  
% 2.13/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.13/0.95  
% 2.13/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.13/0.95  ------ Proving...
% 2.13/0.95  ------ Problem Properties 
% 2.13/0.95  
% 2.13/0.95  
% 2.13/0.95  clauses                                 13
% 2.13/0.95  conjectures                             3
% 2.13/0.95  EPR                                     2
% 2.13/0.95  Horn                                    10
% 2.13/0.95  unary                                   4
% 2.13/0.95  binary                                  6
% 2.13/0.95  lits                                    25
% 2.13/0.95  lits eq                                 7
% 2.13/0.95  fd_pure                                 0
% 2.13/0.95  fd_pseudo                               0
% 2.13/0.95  fd_cond                                 2
% 2.13/0.95  fd_pseudo_cond                          0
% 2.13/0.95  AC symbols                              0
% 2.13/0.95  
% 2.13/0.95  ------ Schedule dynamic 5 is on 
% 2.13/0.95  
% 2.13/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.13/0.95  
% 2.13/0.95  
% 2.13/0.95  ------ 
% 2.13/0.95  Current options:
% 2.13/0.95  ------ 
% 2.13/0.95  
% 2.13/0.95  ------ Input Options
% 2.13/0.95  
% 2.13/0.95  --out_options                           all
% 2.13/0.95  --tptp_safe_out                         true
% 2.13/0.95  --problem_path                          ""
% 2.13/0.95  --include_path                          ""
% 2.13/0.95  --clausifier                            res/vclausify_rel
% 2.13/0.95  --clausifier_options                    --mode clausify
% 2.13/0.95  --stdin                                 false
% 2.13/0.95  --stats_out                             all
% 2.13/0.95  
% 2.13/0.95  ------ General Options
% 2.13/0.95  
% 2.13/0.95  --fof                                   false
% 2.13/0.95  --time_out_real                         305.
% 2.13/0.95  --time_out_virtual                      -1.
% 2.13/0.95  --symbol_type_check                     false
% 2.13/0.95  --clausify_out                          false
% 2.13/0.95  --sig_cnt_out                           false
% 2.13/0.95  --trig_cnt_out                          false
% 2.13/0.95  --trig_cnt_out_tolerance                1.
% 2.13/0.95  --trig_cnt_out_sk_spl                   false
% 2.13/0.95  --abstr_cl_out                          false
% 2.13/0.95  
% 2.13/0.95  ------ Global Options
% 2.13/0.95  
% 2.13/0.95  --schedule                              default
% 2.13/0.95  --add_important_lit                     false
% 2.13/0.95  --prop_solver_per_cl                    1000
% 2.13/0.95  --min_unsat_core                        false
% 2.13/0.95  --soft_assumptions                      false
% 2.13/0.95  --soft_lemma_size                       3
% 2.13/0.95  --prop_impl_unit_size                   0
% 2.13/0.95  --prop_impl_unit                        []
% 2.13/0.95  --share_sel_clauses                     true
% 2.13/0.95  --reset_solvers                         false
% 2.13/0.95  --bc_imp_inh                            [conj_cone]
% 2.13/0.95  --conj_cone_tolerance                   3.
% 2.13/0.95  --extra_neg_conj                        none
% 2.13/0.95  --large_theory_mode                     true
% 2.13/0.95  --prolific_symb_bound                   200
% 2.13/0.95  --lt_threshold                          2000
% 2.13/0.95  --clause_weak_htbl                      true
% 2.13/0.95  --gc_record_bc_elim                     false
% 2.13/0.95  
% 2.13/0.95  ------ Preprocessing Options
% 2.13/0.95  
% 2.13/0.95  --preprocessing_flag                    true
% 2.13/0.95  --time_out_prep_mult                    0.1
% 2.13/0.95  --splitting_mode                        input
% 2.13/0.95  --splitting_grd                         true
% 2.13/0.95  --splitting_cvd                         false
% 2.13/0.95  --splitting_cvd_svl                     false
% 2.13/0.95  --splitting_nvd                         32
% 2.13/0.95  --sub_typing                            true
% 2.13/0.95  --prep_gs_sim                           true
% 2.13/0.95  --prep_unflatten                        true
% 2.13/0.95  --prep_res_sim                          true
% 2.13/0.95  --prep_upred                            true
% 2.13/0.95  --prep_sem_filter                       exhaustive
% 2.13/0.95  --prep_sem_filter_out                   false
% 2.13/0.95  --pred_elim                             true
% 2.13/0.95  --res_sim_input                         true
% 2.13/0.95  --eq_ax_congr_red                       true
% 2.13/0.95  --pure_diseq_elim                       true
% 2.13/0.95  --brand_transform                       false
% 2.13/0.95  --non_eq_to_eq                          false
% 2.13/0.95  --prep_def_merge                        true
% 2.13/0.95  --prep_def_merge_prop_impl              false
% 2.13/0.95  --prep_def_merge_mbd                    true
% 2.13/0.95  --prep_def_merge_tr_red                 false
% 2.13/0.95  --prep_def_merge_tr_cl                  false
% 2.13/0.95  --smt_preprocessing                     true
% 2.13/0.95  --smt_ac_axioms                         fast
% 2.13/0.95  --preprocessed_out                      false
% 2.13/0.95  --preprocessed_stats                    false
% 2.13/0.95  
% 2.13/0.95  ------ Abstraction refinement Options
% 2.13/0.95  
% 2.13/0.95  --abstr_ref                             []
% 2.13/0.95  --abstr_ref_prep                        false
% 2.13/0.95  --abstr_ref_until_sat                   false
% 2.13/0.95  --abstr_ref_sig_restrict                funpre
% 2.13/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.95  --abstr_ref_under                       []
% 2.13/0.95  
% 2.13/0.95  ------ SAT Options
% 2.13/0.95  
% 2.13/0.95  --sat_mode                              false
% 2.13/0.95  --sat_fm_restart_options                ""
% 2.13/0.95  --sat_gr_def                            false
% 2.13/0.95  --sat_epr_types                         true
% 2.13/0.95  --sat_non_cyclic_types                  false
% 2.13/0.95  --sat_finite_models                     false
% 2.13/0.95  --sat_fm_lemmas                         false
% 2.13/0.95  --sat_fm_prep                           false
% 2.13/0.95  --sat_fm_uc_incr                        true
% 2.13/0.95  --sat_out_model                         small
% 2.13/0.95  --sat_out_clauses                       false
% 2.13/0.95  
% 2.13/0.95  ------ QBF Options
% 2.13/0.95  
% 2.13/0.95  --qbf_mode                              false
% 2.13/0.95  --qbf_elim_univ                         false
% 2.13/0.95  --qbf_dom_inst                          none
% 2.13/0.95  --qbf_dom_pre_inst                      false
% 2.13/0.95  --qbf_sk_in                             false
% 2.13/0.95  --qbf_pred_elim                         true
% 2.13/0.95  --qbf_split                             512
% 2.13/0.95  
% 2.13/0.95  ------ BMC1 Options
% 2.13/0.95  
% 2.13/0.95  --bmc1_incremental                      false
% 2.13/0.95  --bmc1_axioms                           reachable_all
% 2.13/0.95  --bmc1_min_bound                        0
% 2.13/0.95  --bmc1_max_bound                        -1
% 2.13/0.95  --bmc1_max_bound_default                -1
% 2.13/0.95  --bmc1_symbol_reachability              true
% 2.13/0.95  --bmc1_property_lemmas                  false
% 2.13/0.95  --bmc1_k_induction                      false
% 2.13/0.95  --bmc1_non_equiv_states                 false
% 2.13/0.95  --bmc1_deadlock                         false
% 2.13/0.95  --bmc1_ucm                              false
% 2.13/0.95  --bmc1_add_unsat_core                   none
% 2.13/0.95  --bmc1_unsat_core_children              false
% 2.13/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/0.95  --bmc1_out_stat                         full
% 2.13/0.95  --bmc1_ground_init                      false
% 2.13/0.95  --bmc1_pre_inst_next_state              false
% 2.13/0.95  --bmc1_pre_inst_state                   false
% 2.13/0.95  --bmc1_pre_inst_reach_state             false
% 2.13/0.95  --bmc1_out_unsat_core                   false
% 2.13/0.95  --bmc1_aig_witness_out                  false
% 2.13/0.95  --bmc1_verbose                          false
% 2.13/0.95  --bmc1_dump_clauses_tptp                false
% 2.13/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.13/0.95  --bmc1_dump_file                        -
% 2.13/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.13/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.13/0.95  --bmc1_ucm_extend_mode                  1
% 2.13/0.95  --bmc1_ucm_init_mode                    2
% 2.13/0.95  --bmc1_ucm_cone_mode                    none
% 2.13/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.13/0.95  --bmc1_ucm_relax_model                  4
% 2.13/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.13/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/0.95  --bmc1_ucm_layered_model                none
% 2.13/0.95  --bmc1_ucm_max_lemma_size               10
% 2.13/0.95  
% 2.13/0.95  ------ AIG Options
% 2.13/0.95  
% 2.13/0.95  --aig_mode                              false
% 2.13/0.95  
% 2.13/0.95  ------ Instantiation Options
% 2.13/0.95  
% 2.13/0.95  --instantiation_flag                    true
% 2.13/0.95  --inst_sos_flag                         false
% 2.13/0.95  --inst_sos_phase                        true
% 2.13/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/0.95  --inst_lit_sel_side                     none
% 2.13/0.95  --inst_solver_per_active                1400
% 2.13/0.95  --inst_solver_calls_frac                1.
% 2.13/0.95  --inst_passive_queue_type               priority_queues
% 2.13/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/0.95  --inst_passive_queues_freq              [25;2]
% 2.13/0.95  --inst_dismatching                      true
% 2.13/0.95  --inst_eager_unprocessed_to_passive     true
% 2.13/0.95  --inst_prop_sim_given                   true
% 2.13/0.95  --inst_prop_sim_new                     false
% 2.13/0.95  --inst_subs_new                         false
% 2.13/0.95  --inst_eq_res_simp                      false
% 2.13/0.95  --inst_subs_given                       false
% 2.13/0.95  --inst_orphan_elimination               true
% 2.13/0.95  --inst_learning_loop_flag               true
% 2.13/0.95  --inst_learning_start                   3000
% 2.13/0.95  --inst_learning_factor                  2
% 2.13/0.95  --inst_start_prop_sim_after_learn       3
% 2.13/0.95  --inst_sel_renew                        solver
% 2.13/0.95  --inst_lit_activity_flag                true
% 2.13/0.95  --inst_restr_to_given                   false
% 2.13/0.95  --inst_activity_threshold               500
% 2.13/0.95  --inst_out_proof                        true
% 2.13/0.95  
% 2.13/0.95  ------ Resolution Options
% 2.13/0.95  
% 2.13/0.95  --resolution_flag                       false
% 2.13/0.95  --res_lit_sel                           adaptive
% 2.13/0.95  --res_lit_sel_side                      none
% 2.13/0.95  --res_ordering                          kbo
% 2.13/0.95  --res_to_prop_solver                    active
% 2.13/0.95  --res_prop_simpl_new                    false
% 2.13/0.95  --res_prop_simpl_given                  true
% 2.13/0.95  --res_passive_queue_type                priority_queues
% 2.13/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/0.95  --res_passive_queues_freq               [15;5]
% 2.13/0.95  --res_forward_subs                      full
% 2.13/0.95  --res_backward_subs                     full
% 2.13/0.95  --res_forward_subs_resolution           true
% 2.13/0.95  --res_backward_subs_resolution          true
% 2.13/0.95  --res_orphan_elimination                true
% 2.13/0.95  --res_time_limit                        2.
% 2.13/0.95  --res_out_proof                         true
% 2.13/0.95  
% 2.13/0.95  ------ Superposition Options
% 2.13/0.95  
% 2.13/0.95  --superposition_flag                    true
% 2.13/0.95  --sup_passive_queue_type                priority_queues
% 2.13/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.13/0.95  --demod_completeness_check              fast
% 2.13/0.95  --demod_use_ground                      true
% 2.13/0.95  --sup_to_prop_solver                    passive
% 2.13/0.95  --sup_prop_simpl_new                    true
% 2.13/0.95  --sup_prop_simpl_given                  true
% 2.13/0.95  --sup_fun_splitting                     false
% 2.13/0.95  --sup_smt_interval                      50000
% 2.13/0.95  
% 2.13/0.95  ------ Superposition Simplification Setup
% 2.13/0.95  
% 2.13/0.95  --sup_indices_passive                   []
% 2.13/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.95  --sup_full_bw                           [BwDemod]
% 2.13/0.95  --sup_immed_triv                        [TrivRules]
% 2.13/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.95  --sup_immed_bw_main                     []
% 2.13/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.95  
% 2.13/0.95  ------ Combination Options
% 2.13/0.95  
% 2.13/0.95  --comb_res_mult                         3
% 2.13/0.95  --comb_sup_mult                         2
% 2.13/0.95  --comb_inst_mult                        10
% 2.13/0.95  
% 2.13/0.95  ------ Debug Options
% 2.13/0.95  
% 2.13/0.95  --dbg_backtrace                         false
% 2.13/0.95  --dbg_dump_prop_clauses                 false
% 2.13/0.95  --dbg_dump_prop_clauses_file            -
% 2.13/0.95  --dbg_out_stat                          false
% 2.13/0.95  
% 2.13/0.95  
% 2.13/0.95  
% 2.13/0.95  
% 2.13/0.95  ------ Proving...
% 2.13/0.95  
% 2.13/0.95  
% 2.13/0.95  % SZS status Theorem for theBenchmark.p
% 2.13/0.95  
% 2.13/0.95   Resolution empty clause
% 2.13/0.95  
% 2.13/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.13/0.95  
% 2.13/0.95  fof(f1,axiom,(
% 2.13/0.95    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.13/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.95  
% 2.13/0.95  fof(f7,plain,(
% 2.13/0.95    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.13/0.95    inference(ennf_transformation,[],[f1])).
% 2.13/0.95  
% 2.13/0.95  fof(f11,plain,(
% 2.13/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.13/0.95    inference(nnf_transformation,[],[f7])).
% 2.13/0.95  
% 2.13/0.95  fof(f12,plain,(
% 2.13/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.13/0.95    inference(rectify,[],[f11])).
% 2.13/0.95  
% 2.13/0.95  fof(f13,plain,(
% 2.13/0.95    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.13/0.95    introduced(choice_axiom,[])).
% 2.13/0.95  
% 2.13/0.95  fof(f14,plain,(
% 2.13/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.13/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 2.13/0.95  
% 2.13/0.95  fof(f24,plain,(
% 2.13/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.13/0.95    inference(cnf_transformation,[],[f14])).
% 2.13/0.95  
% 2.13/0.95  fof(f2,axiom,(
% 2.13/0.95    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.13/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.95  
% 2.13/0.95  fof(f8,plain,(
% 2.13/0.95    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.13/0.95    inference(ennf_transformation,[],[f2])).
% 2.13/0.95  
% 2.13/0.95  fof(f15,plain,(
% 2.13/0.95    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.13/0.95    introduced(choice_axiom,[])).
% 2.13/0.95  
% 2.13/0.95  fof(f16,plain,(
% 2.13/0.95    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.13/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f8,f15])).
% 2.13/0.95  
% 2.13/0.95  fof(f26,plain,(
% 2.13/0.95    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.13/0.95    inference(cnf_transformation,[],[f16])).
% 2.13/0.95  
% 2.13/0.95  fof(f5,conjecture,(
% 2.13/0.95    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.13/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.95  
% 2.13/0.95  fof(f6,negated_conjecture,(
% 2.13/0.95    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 2.13/0.95    inference(negated_conjecture,[],[f5])).
% 2.13/0.95  
% 2.13/0.95  fof(f9,plain,(
% 2.13/0.95    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.13/0.95    inference(ennf_transformation,[],[f6])).
% 2.13/0.95  
% 2.13/0.95  fof(f10,plain,(
% 2.13/0.95    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 2.13/0.95    inference(flattening,[],[f9])).
% 2.13/0.95  
% 2.13/0.95  fof(f21,plain,(
% 2.13/0.95    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)) & k1_xboole_0 != k2_zfmisc_1(sK2,sK3) & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))),
% 2.13/0.95    introduced(choice_axiom,[])).
% 2.13/0.95  
% 2.13/0.95  fof(f22,plain,(
% 2.13/0.95    (~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)) & k1_xboole_0 != k2_zfmisc_1(sK2,sK3) & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))),
% 2.13/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f10,f21])).
% 2.13/0.95  
% 2.13/0.95  fof(f33,plain,(
% 2.13/0.95    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))),
% 2.13/0.95    inference(cnf_transformation,[],[f22])).
% 2.13/0.95  
% 2.13/0.95  fof(f3,axiom,(
% 2.13/0.95    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.13/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.95  
% 2.13/0.95  fof(f17,plain,(
% 2.13/0.95    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.13/0.95    inference(nnf_transformation,[],[f3])).
% 2.13/0.95  
% 2.13/0.95  fof(f18,plain,(
% 2.13/0.95    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.13/0.95    inference(flattening,[],[f17])).
% 2.13/0.95  
% 2.13/0.95  fof(f29,plain,(
% 2.13/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.13/0.95    inference(cnf_transformation,[],[f18])).
% 2.13/0.95  
% 2.13/0.95  fof(f23,plain,(
% 2.13/0.95    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.13/0.95    inference(cnf_transformation,[],[f14])).
% 2.13/0.95  
% 2.13/0.95  fof(f28,plain,(
% 2.13/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.13/0.95    inference(cnf_transformation,[],[f18])).
% 2.13/0.95  
% 2.13/0.95  fof(f25,plain,(
% 2.13/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.13/0.95    inference(cnf_transformation,[],[f14])).
% 2.13/0.95  
% 2.13/0.95  fof(f27,plain,(
% 2.13/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.13/0.95    inference(cnf_transformation,[],[f18])).
% 2.13/0.95  
% 2.13/0.95  fof(f35,plain,(
% 2.13/0.95    ~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)),
% 2.13/0.95    inference(cnf_transformation,[],[f22])).
% 2.13/0.95  
% 2.13/0.95  fof(f34,plain,(
% 2.13/0.95    k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 2.13/0.95    inference(cnf_transformation,[],[f22])).
% 2.13/0.95  
% 2.13/0.95  fof(f4,axiom,(
% 2.13/0.95    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.13/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/0.95  
% 2.13/0.95  fof(f19,plain,(
% 2.13/0.95    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.13/0.95    inference(nnf_transformation,[],[f4])).
% 2.13/0.95  
% 2.13/0.95  fof(f20,plain,(
% 2.13/0.95    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.13/0.95    inference(flattening,[],[f19])).
% 2.13/0.95  
% 2.13/0.95  fof(f31,plain,(
% 2.13/0.95    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.13/0.95    inference(cnf_transformation,[],[f20])).
% 2.13/0.95  
% 2.13/0.95  fof(f37,plain,(
% 2.13/0.95    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.13/0.95    inference(equality_resolution,[],[f31])).
% 2.13/0.95  
% 2.13/0.95  fof(f32,plain,(
% 2.13/0.95    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.13/0.95    inference(cnf_transformation,[],[f20])).
% 2.13/0.95  
% 2.13/0.95  fof(f36,plain,(
% 2.13/0.95    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.13/0.95    inference(equality_resolution,[],[f32])).
% 2.13/0.95  
% 2.13/0.95  cnf(c_1,plain,
% 2.13/0.95      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.13/0.95      inference(cnf_transformation,[],[f24]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_291,plain,
% 2.13/0.95      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.13/0.95      | r1_tarski(X0,X1) = iProver_top ),
% 2.13/0.95      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_3,plain,
% 2.13/0.95      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.13/0.95      inference(cnf_transformation,[],[f26]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_289,plain,
% 2.13/0.95      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.13/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_12,negated_conjecture,
% 2.13/0.95      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
% 2.13/0.95      inference(cnf_transformation,[],[f33]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_284,plain,
% 2.13/0.95      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 2.13/0.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_4,plain,
% 2.13/0.95      ( ~ r2_hidden(X0,X1)
% 2.13/0.95      | ~ r2_hidden(X2,X3)
% 2.13/0.95      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.13/0.95      inference(cnf_transformation,[],[f29]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_288,plain,
% 2.13/0.95      ( r2_hidden(X0,X1) != iProver_top
% 2.13/0.95      | r2_hidden(X2,X3) != iProver_top
% 2.13/0.95      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 2.13/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_2,plain,
% 2.13/0.95      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.13/0.95      inference(cnf_transformation,[],[f23]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_290,plain,
% 2.13/0.95      ( r2_hidden(X0,X1) != iProver_top
% 2.13/0.95      | r2_hidden(X0,X2) = iProver_top
% 2.13/0.95      | r1_tarski(X1,X2) != iProver_top ),
% 2.13/0.95      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_874,plain,
% 2.13/0.95      ( r2_hidden(X0,X1) != iProver_top
% 2.13/0.95      | r2_hidden(X2,X3) != iProver_top
% 2.13/0.95      | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
% 2.13/0.95      | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_288,c_290]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_1166,plain,
% 2.13/0.95      ( r2_hidden(X0,sK2) != iProver_top
% 2.13/0.95      | r2_hidden(X1,sK3) != iProver_top
% 2.13/0.95      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_284,c_874]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_5,plain,
% 2.13/0.95      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.13/0.95      inference(cnf_transformation,[],[f28]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_287,plain,
% 2.13/0.95      ( r2_hidden(X0,X1) = iProver_top
% 2.13/0.95      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 2.13/0.95      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_1206,plain,
% 2.13/0.95      ( r2_hidden(X0,sK2) != iProver_top
% 2.13/0.95      | r2_hidden(X1,sK5) = iProver_top
% 2.13/0.95      | r2_hidden(X1,sK3) != iProver_top ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_1166,c_287]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_1860,plain,
% 2.13/0.95      ( sK2 = k1_xboole_0
% 2.13/0.95      | r2_hidden(X0,sK5) = iProver_top
% 2.13/0.95      | r2_hidden(X0,sK3) != iProver_top ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_289,c_1206]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_3440,plain,
% 2.13/0.95      ( sK2 = k1_xboole_0
% 2.13/0.95      | r2_hidden(sK0(sK3,X0),sK5) = iProver_top
% 2.13/0.95      | r1_tarski(sK3,X0) = iProver_top ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_291,c_1860]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_0,plain,
% 2.13/0.95      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.13/0.95      inference(cnf_transformation,[],[f25]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_292,plain,
% 2.13/0.95      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.13/0.95      | r1_tarski(X0,X1) = iProver_top ),
% 2.13/0.95      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_8601,plain,
% 2.13/0.95      ( sK2 = k1_xboole_0 | r1_tarski(sK3,sK5) = iProver_top ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_3440,c_292]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_6,plain,
% 2.13/0.95      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.13/0.95      inference(cnf_transformation,[],[f27]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_286,plain,
% 2.13/0.95      ( r2_hidden(X0,X1) = iProver_top
% 2.13/0.95      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 2.13/0.95      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_1207,plain,
% 2.13/0.95      ( r2_hidden(X0,sK4) = iProver_top
% 2.13/0.95      | r2_hidden(X0,sK2) != iProver_top
% 2.13/0.95      | r2_hidden(X1,sK3) != iProver_top ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_1166,c_286]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_1997,plain,
% 2.13/0.95      ( r2_hidden(X0,sK3) != iProver_top
% 2.13/0.95      | r2_hidden(sK0(sK2,X1),sK4) = iProver_top
% 2.13/0.95      | r1_tarski(sK2,X1) = iProver_top ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_291,c_1207]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_9719,plain,
% 2.13/0.95      ( sK3 = k1_xboole_0
% 2.13/0.95      | r2_hidden(sK0(sK2,X0),sK4) = iProver_top
% 2.13/0.95      | r1_tarski(sK2,X0) = iProver_top ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_289,c_1997]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_10154,plain,
% 2.13/0.95      ( sK3 = k1_xboole_0 | r1_tarski(sK2,sK4) = iProver_top ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_9719,c_292]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_10,negated_conjecture,
% 2.13/0.95      ( ~ r1_tarski(sK2,sK4) | ~ r1_tarski(sK3,sK5) ),
% 2.13/0.95      inference(cnf_transformation,[],[f35]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_285,plain,
% 2.13/0.95      ( r1_tarski(sK2,sK4) != iProver_top | r1_tarski(sK3,sK5) != iProver_top ),
% 2.13/0.95      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_10288,plain,
% 2.13/0.95      ( sK3 = k1_xboole_0 | r1_tarski(sK3,sK5) != iProver_top ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_10154,c_285]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_10293,plain,
% 2.13/0.95      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_8601,c_10288]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_11,negated_conjecture,
% 2.13/0.95      ( k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
% 2.13/0.95      inference(cnf_transformation,[],[f34]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_10349,plain,
% 2.13/0.95      ( k2_zfmisc_1(k1_xboole_0,sK3) != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.13/0.95      inference(superposition,[status(thm)],[c_10293,c_11]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_8,plain,
% 2.13/0.95      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.13/0.95      inference(cnf_transformation,[],[f37]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_10352,plain,
% 2.13/0.95      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.13/0.95      inference(demodulation,[status(thm)],[c_10349,c_8]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_10353,plain,
% 2.13/0.95      ( sK3 = k1_xboole_0 ),
% 2.13/0.95      inference(equality_resolution_simp,[status(thm)],[c_10352]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_10397,plain,
% 2.13/0.95      ( k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0 ),
% 2.13/0.95      inference(demodulation,[status(thm)],[c_10353,c_11]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_7,plain,
% 2.13/0.95      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.13/0.95      inference(cnf_transformation,[],[f36]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_10399,plain,
% 2.13/0.95      ( k1_xboole_0 != k1_xboole_0 ),
% 2.13/0.95      inference(demodulation,[status(thm)],[c_10397,c_7]) ).
% 2.13/0.95  
% 2.13/0.95  cnf(c_10400,plain,
% 2.13/0.95      ( $false ),
% 2.13/0.95      inference(equality_resolution_simp,[status(thm)],[c_10399]) ).
% 2.13/0.95  
% 2.13/0.95  
% 2.13/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.13/0.95  
% 2.13/0.95  ------                               Statistics
% 2.13/0.95  
% 2.13/0.95  ------ General
% 2.13/0.95  
% 2.13/0.95  abstr_ref_over_cycles:                  0
% 2.13/0.95  abstr_ref_under_cycles:                 0
% 2.13/0.95  gc_basic_clause_elim:                   0
% 2.13/0.95  forced_gc_time:                         0
% 2.13/0.95  parsing_time:                           0.008
% 2.13/0.95  unif_index_cands_time:                  0.
% 2.13/0.95  unif_index_add_time:                    0.
% 2.13/0.95  orderings_time:                         0.
% 2.13/0.95  out_proof_time:                         0.007
% 2.13/0.95  total_time:                             0.294
% 2.13/0.95  num_of_symbols:                         42
% 2.13/0.95  num_of_terms:                           8113
% 2.13/0.95  
% 2.13/0.95  ------ Preprocessing
% 2.13/0.95  
% 2.13/0.95  num_of_splits:                          0
% 2.13/0.95  num_of_split_atoms:                     0
% 2.13/0.95  num_of_reused_defs:                     0
% 2.13/0.95  num_eq_ax_congr_red:                    10
% 2.13/0.95  num_of_sem_filtered_clauses:            1
% 2.13/0.95  num_of_subtypes:                        0
% 2.13/0.95  monotx_restored_types:                  0
% 2.13/0.95  sat_num_of_epr_types:                   0
% 2.13/0.95  sat_num_of_non_cyclic_types:            0
% 2.13/0.95  sat_guarded_non_collapsed_types:        0
% 2.13/0.95  num_pure_diseq_elim:                    0
% 2.13/0.95  simp_replaced_by:                       0
% 2.13/0.95  res_preprocessed:                       50
% 2.13/0.95  prep_upred:                             0
% 2.13/0.95  prep_unflattend:                        0
% 2.13/0.95  smt_new_axioms:                         0
% 2.13/0.95  pred_elim_cands:                        2
% 2.13/0.95  pred_elim:                              0
% 2.13/0.95  pred_elim_cl:                           0
% 2.13/0.95  pred_elim_cycles:                       1
% 2.13/0.95  merged_defs:                            0
% 2.13/0.95  merged_defs_ncl:                        0
% 2.13/0.95  bin_hyper_res:                          0
% 2.13/0.95  prep_cycles:                            3
% 2.13/0.95  pred_elim_time:                         0.
% 2.13/0.95  splitting_time:                         0.
% 2.13/0.95  sem_filter_time:                        0.
% 2.13/0.95  monotx_time:                            0.
% 2.13/0.95  subtype_inf_time:                       0.
% 2.13/0.95  
% 2.13/0.95  ------ Problem properties
% 2.13/0.95  
% 2.13/0.95  clauses:                                13
% 2.13/0.95  conjectures:                            3
% 2.13/0.95  epr:                                    2
% 2.13/0.95  horn:                                   10
% 2.13/0.95  ground:                                 3
% 2.13/0.95  unary:                                  4
% 2.13/0.95  binary:                                 6
% 2.13/0.95  lits:                                   25
% 2.13/0.95  lits_eq:                                7
% 2.13/0.95  fd_pure:                                0
% 2.13/0.95  fd_pseudo:                              0
% 2.13/0.95  fd_cond:                                2
% 2.13/0.95  fd_pseudo_cond:                         0
% 2.13/0.95  ac_symbols:                             0
% 2.13/0.95  
% 2.13/0.95  ------ Propositional Solver
% 2.13/0.95  
% 2.13/0.95  prop_solver_calls:                      26
% 2.13/0.95  prop_fast_solver_calls:                 509
% 2.13/0.95  smt_solver_calls:                       0
% 2.13/0.95  smt_fast_solver_calls:                  0
% 2.13/0.95  prop_num_of_clauses:                    3178
% 2.13/0.95  prop_preprocess_simplified:             5766
% 2.13/0.95  prop_fo_subsumed:                       1
% 2.13/0.95  prop_solver_time:                       0.
% 2.13/0.95  smt_solver_time:                        0.
% 2.13/0.95  smt_fast_solver_time:                   0.
% 2.13/0.95  prop_fast_solver_time:                  0.
% 2.13/0.95  prop_unsat_core_time:                   0.
% 2.13/0.95  
% 2.13/0.95  ------ QBF
% 2.13/0.95  
% 2.13/0.95  qbf_q_res:                              0
% 2.13/0.95  qbf_num_tautologies:                    0
% 2.13/0.95  qbf_prep_cycles:                        0
% 2.13/0.95  
% 2.13/0.95  ------ BMC1
% 2.13/0.95  
% 2.13/0.95  bmc1_current_bound:                     -1
% 2.13/0.95  bmc1_last_solved_bound:                 -1
% 2.13/0.95  bmc1_unsat_core_size:                   -1
% 2.13/0.95  bmc1_unsat_core_parents_size:           -1
% 2.13/0.95  bmc1_merge_next_fun:                    0
% 2.13/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.13/0.95  
% 2.13/0.95  ------ Instantiation
% 2.13/0.95  
% 2.13/0.95  inst_num_of_clauses:                    809
% 2.13/0.95  inst_num_in_passive:                    423
% 2.13/0.95  inst_num_in_active:                     275
% 2.13/0.95  inst_num_in_unprocessed:                111
% 2.13/0.95  inst_num_of_loops:                      390
% 2.13/0.95  inst_num_of_learning_restarts:          0
% 2.13/0.95  inst_num_moves_active_passive:          112
% 2.13/0.95  inst_lit_activity:                      0
% 2.13/0.95  inst_lit_activity_moves:                1
% 2.13/0.95  inst_num_tautologies:                   0
% 2.13/0.95  inst_num_prop_implied:                  0
% 2.13/0.95  inst_num_existing_simplified:           0
% 2.13/0.95  inst_num_eq_res_simplified:             0
% 2.13/0.95  inst_num_child_elim:                    0
% 2.13/0.95  inst_num_of_dismatching_blockings:      33
% 2.13/0.95  inst_num_of_non_proper_insts:           472
% 2.13/0.95  inst_num_of_duplicates:                 0
% 2.13/0.95  inst_inst_num_from_inst_to_res:         0
% 2.13/0.95  inst_dismatching_checking_time:         0.
% 2.13/0.95  
% 2.13/0.95  ------ Resolution
% 2.13/0.95  
% 2.13/0.95  res_num_of_clauses:                     0
% 2.13/0.95  res_num_in_passive:                     0
% 2.13/0.95  res_num_in_active:                      0
% 2.13/0.95  res_num_of_loops:                       53
% 2.13/0.95  res_forward_subset_subsumed:            9
% 2.13/0.95  res_backward_subset_subsumed:           0
% 2.13/0.95  res_forward_subsumed:                   0
% 2.13/0.95  res_backward_subsumed:                  0
% 2.13/0.95  res_forward_subsumption_resolution:     0
% 2.13/0.95  res_backward_subsumption_resolution:    0
% 2.13/0.95  res_clause_to_clause_subsumption:       5771
% 2.13/0.95  res_orphan_elimination:                 0
% 2.13/0.95  res_tautology_del:                      64
% 2.13/0.95  res_num_eq_res_simplified:              0
% 2.13/0.95  res_num_sel_changes:                    0
% 2.13/0.95  res_moves_from_active_to_pass:          0
% 2.13/0.95  
% 2.13/0.95  ------ Superposition
% 2.13/0.95  
% 2.13/0.95  sup_time_total:                         0.
% 2.13/0.95  sup_time_generating:                    0.
% 2.13/0.95  sup_time_sim_full:                      0.
% 2.13/0.95  sup_time_sim_immed:                     0.
% 2.13/0.95  
% 2.13/0.95  sup_num_of_clauses:                     271
% 2.13/0.95  sup_num_in_active:                      29
% 2.13/0.95  sup_num_in_passive:                     242
% 2.13/0.95  sup_num_of_loops:                       77
% 2.13/0.95  sup_fw_superposition:                   222
% 2.13/0.95  sup_bw_superposition:                   344
% 2.13/0.95  sup_immediate_simplified:               104
% 2.13/0.95  sup_given_eliminated:                   2
% 2.13/0.95  comparisons_done:                       0
% 2.13/0.95  comparisons_avoided:                    0
% 2.13/0.95  
% 2.13/0.95  ------ Simplifications
% 2.13/0.95  
% 2.13/0.95  
% 2.13/0.95  sim_fw_subset_subsumed:                 27
% 2.13/0.95  sim_bw_subset_subsumed:                 42
% 2.13/0.95  sim_fw_subsumed:                        69
% 2.13/0.95  sim_bw_subsumed:                        22
% 2.13/0.95  sim_fw_subsumption_res:                 0
% 2.13/0.95  sim_bw_subsumption_res:                 0
% 2.13/0.95  sim_tautology_del:                      3
% 2.13/0.95  sim_eq_tautology_del:                   7
% 2.13/0.95  sim_eq_res_simp:                        1
% 2.13/0.95  sim_fw_demodulated:                     2
% 2.13/0.95  sim_bw_demodulated:                     40
% 2.13/0.95  sim_light_normalised:                   0
% 2.13/0.95  sim_joinable_taut:                      0
% 2.13/0.95  sim_joinable_simp:                      0
% 2.13/0.95  sim_ac_normalised:                      0
% 2.13/0.95  sim_smt_subsumption:                    0
% 2.13/0.95  
%------------------------------------------------------------------------------
