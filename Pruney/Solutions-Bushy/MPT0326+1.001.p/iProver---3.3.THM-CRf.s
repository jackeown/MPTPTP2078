%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0326+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:00 EST 2020

% Result     : Theorem 1.27s
% Output     : CNFRefutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 222 expanded)
%              Number of clauses        :   36 (  91 expanded)
%              Number of leaves         :    8 (  51 expanded)
%              Depth                    :   19
%              Number of atoms          :  152 ( 593 expanded)
%              Number of equality atoms :   85 ( 207 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
     => ( ~ r1_tarski(sK2,sK4)
        & ( r1_tarski(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK4,sK3))
          | r1_tarski(k2_zfmisc_1(X0,sK2),k2_zfmisc_1(sK3,sK4)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK1,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_tarski(sK2,sK4)
    & ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK4,sK3))
      | r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) )
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f18,f17])).

fof(f30,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK4,sK3))
    | r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ~ r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_244,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK4,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))
    | k2_zfmisc_1(X2,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_248,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X3,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_102,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_103,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_102])).

cnf(c_285,plain,
    ( k2_zfmisc_1(X0,X1) = o_0_0_xboole_0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X3,X2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_248,c_103])).

cnf(c_579,plain,
    ( k2_zfmisc_1(sK1,sK2) = o_0_0_xboole_0
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK4,sK3)) = iProver_top
    | r1_tarski(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_244,c_285])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,plain,
    ( r1_tarski(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_699,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK4,sK3)) = iProver_top
    | k2_zfmisc_1(sK1,sK2) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_14])).

cnf(c_700,plain,
    ( k2_zfmisc_1(sK1,sK2) = o_0_0_xboole_0
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK4,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
    | k2_zfmisc_1(X0,X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_247,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_278,plain,
    ( k2_zfmisc_1(X0,X1) = o_0_0_xboole_0
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_247,c_103])).

cnf(c_706,plain,
    ( k2_zfmisc_1(sK1,sK2) = o_0_0_xboole_0
    | k2_zfmisc_1(sK2,sK1) = o_0_0_xboole_0
    | r1_tarski(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_700,c_278])).

cnf(c_713,plain,
    ( r1_tarski(sK2,sK4)
    | k2_zfmisc_1(sK1,sK2) = o_0_0_xboole_0
    | k2_zfmisc_1(sK2,sK1) = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_706])).

cnf(c_715,plain,
    ( k2_zfmisc_1(sK2,sK1) = o_0_0_xboole_0
    | k2_zfmisc_1(sK1,sK2) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_706,c_9,c_713])).

cnf(c_716,plain,
    ( k2_zfmisc_1(sK1,sK2) = o_0_0_xboole_0
    | k2_zfmisc_1(sK2,sK1) = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_715])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_266,plain,
    ( k2_zfmisc_1(X0,X1) != o_0_0_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_103])).

cnf(c_267,plain,
    ( k2_zfmisc_1(X0,X1) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1 ),
    inference(demodulation,[status(thm)],[c_266,c_103])).

cnf(c_722,plain,
    ( k2_zfmisc_1(sK2,sK1) = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_716,c_267])).

cnf(c_11,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_107,plain,
    ( sK1 != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_816,plain,
    ( k2_zfmisc_1(sK2,sK1) = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_107])).

cnf(c_823,plain,
    ( sK1 = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_816,c_267])).

cnf(c_964,plain,
    ( sK2 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_823,c_107])).

cnf(c_245,plain,
    ( r1_tarski(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_972,plain,
    ( r1_tarski(o_0_0_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_964,c_245])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_246,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_255,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_246,c_103])).

cnf(c_992,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_972,c_255])).


%------------------------------------------------------------------------------
