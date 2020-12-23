%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:37 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  131 (25718 expanded)
%              Number of clauses        :   83 (10041 expanded)
%              Number of leaves         :   15 (8341 expanded)
%              Depth                    :   36
%              Number of atoms          :  382 (132979 expanded)
%              Number of equality atoms :  327 (114297 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( k7_mcart_1(X0,X1,X2,sK3) = sK3
          | k6_mcart_1(X0,X1,X2,sK3) = sK3
          | k5_mcart_1(X0,X1,X2,sK3) = sK3 )
        & m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK0,sK1,sK2,X3) = X3
            | k6_mcart_1(sK0,sK1,sK2,X3) = X3
            | k5_mcart_1(sK0,sK1,sK2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( k7_mcart_1(sK0,sK1,sK2,sK3) = sK3
      | k6_mcart_1(sK0,sK1,sK2,sK3) = sK3
      | k5_mcart_1(sK0,sK1,sK2,sK3) = sK3 )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f23,f22])).

fof(f45,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = sK3
    | k6_mcart_1(sK0,sK1,sK2,sK3) = sK3
    | k5_mcart_1(sK0,sK1,sK2,sK3) = sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) = k3_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2),k2_tarski(X3,X3)) ),
    inference(definition_unfolding,[],[f33,f27,f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X1))
      | k2_tarski(X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f31,f27,f27])).

fof(f52,plain,(
    ! [X1] : r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k2_tarski(X1,X1)) != k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f28,f27,f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
     => ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f32,f27])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_15,negated_conjecture,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = sK3
    | k6_mcart_1(sK0,sK1,sK2,sK3) = sK3
    | k5_mcart_1(sK0,sK1,sK2,sK3) = sK3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_256,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | sK3 != X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_257,plain,
    ( k7_mcart_1(X0,X1,X2,sK3) = k2_mcart_1(sK3)
    | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_737,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_257])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_406,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_431,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_407,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_697,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_698,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_699,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_700,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_701,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_702,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_1026,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_737,c_19,c_18,c_17,c_431,c_698,c_700,c_702])).

cnf(c_1029,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = sK3
    | k5_mcart_1(sK0,sK1,sK2,sK3) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_15,c_1026])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_238,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | sK3 != X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_239,plain,
    ( k6_mcart_1(X0,X1,X2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_750,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_239])).

cnf(c_1153,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_750,c_19,c_18,c_17,c_431,c_698,c_700,c_702])).

cnf(c_1156,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = sK3
    | k2_mcart_1(k1_mcart_1(sK3)) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1029,c_1153])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_220,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | sK3 != X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_221,plain,
    ( k5_mcart_1(X0,X1,X2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_743,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_221])).

cnf(c_1094,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_743,c_19,c_18,c_17,c_431,c_698,c_700,c_702])).

cnf(c_1158,plain,
    ( k1_mcart_1(k1_mcart_1(sK3)) = sK3
    | k2_mcart_1(k1_mcart_1(sK3)) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_1156,c_1094])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
    | k3_mcart_1(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0),k7_mcart_1(X1,X2,X3,X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_274,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
    | sK3 != X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_275,plain,
    ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
    | k3_mcart_1(k5_mcart_1(X0,X1,X2,sK3),k6_mcart_1(X0,X1,X2,sK3),k7_mcart_1(X0,X1,X2,sK3)) = sK3
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_756,plain,
    ( k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) = sK3
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_275])).

cnf(c_1159,plain,
    ( k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_756,c_19,c_18,c_17,c_431,c_698,c_700,c_702])).

cnf(c_1161,plain,
    ( k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_1159,c_1026,c_1094,c_1153])).

cnf(c_7,plain,
    ( k3_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2),k2_tarski(X3,X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_535,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_902,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | r1_tarski(k2_tarski(X0,X0),k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X3,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_535])).

cnf(c_1811,plain,
    ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) = k1_xboole_0
    | r1_tarski(k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))),k2_tarski(sK3,k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),X0,k2_mcart_1(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_902])).

cnf(c_2161,plain,
    ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) = k1_xboole_0
    | r1_tarski(k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1811])).

cnf(c_2202,plain,
    ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK3)) = sK3
    | k2_mcart_1(sK3) = sK3
    | r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1158,c_2161])).

cnf(c_3,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_540,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2863,plain,
    ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK3)) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2202,c_540])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | k3_xboole_0(X1,k2_tarski(X0,X0)) != k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_tarski(X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_167,plain,
    ( k4_xboole_0(X0,k2_tarski(X1,X1)) != X0
    | k3_xboole_0(X0,k2_tarski(X1,X1)) != k2_tarski(X1,X1) ),
    inference(resolution,[status(thm)],[c_2,c_6])).

cnf(c_2866,plain,
    ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) != k3_xboole_0(X0,k1_xboole_0)
    | k4_xboole_0(X0,k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3)))) != X0
    | k2_mcart_1(k1_mcart_1(sK3)) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_2863,c_167])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2918,plain,
    ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) != k1_xboole_0
    | k4_xboole_0(X0,k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3)))) != X0
    | k2_mcart_1(k1_mcart_1(sK3)) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2866,c_0])).

cnf(c_3587,plain,
    ( k4_xboole_0(X0,k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3)))) != X0
    | k2_mcart_1(k1_mcart_1(sK3)) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2918,c_2863])).

cnf(c_3593,plain,
    ( k4_xboole_0(X0,k1_xboole_0) != X0
    | k2_mcart_1(k1_mcart_1(sK3)) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_2863,c_3587])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3605,plain,
    ( X0 != X0
    | k2_mcart_1(k1_mcart_1(sK3)) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3593,c_1])).

cnf(c_3606,plain,
    ( k2_mcart_1(k1_mcart_1(sK3)) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_3605])).

cnf(c_3760,plain,
    ( k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3)) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_3606,c_1161])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k3_zfmisc_1(X1,X0,X2))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_537,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k3_zfmisc_1(X1,X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1468,plain,
    ( k2_tarski(X0,X1) = k1_xboole_0
    | r1_tarski(k2_tarski(X0,X1),k2_tarski(k3_mcart_1(X2,X0,X3),k3_mcart_1(X2,X1,X3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_537])).

cnf(c_3819,plain,
    ( k2_tarski(sK3,X0) = k1_xboole_0
    | k2_mcart_1(sK3) = sK3
    | r1_tarski(k2_tarski(sK3,X0),k2_tarski(sK3,k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),X0,k2_mcart_1(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3760,c_1468])).

cnf(c_4513,plain,
    ( k2_tarski(sK3,sK3) = k1_xboole_0
    | k2_mcart_1(sK3) = sK3
    | r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3760,c_3819])).

cnf(c_5092,plain,
    ( k2_tarski(sK3,sK3) = k1_xboole_0
    | k2_mcart_1(sK3) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4513,c_540])).

cnf(c_5093,plain,
    ( k4_xboole_0(X0,k2_tarski(sK3,sK3)) != X0
    | k3_xboole_0(X0,k1_xboole_0) != k2_tarski(sK3,sK3)
    | k2_mcart_1(sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_5092,c_167])).

cnf(c_5154,plain,
    ( k2_tarski(sK3,sK3) != k1_xboole_0
    | k4_xboole_0(X0,k2_tarski(sK3,sK3)) != X0
    | k2_mcart_1(sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_5093,c_0])).

cnf(c_5243,plain,
    ( k4_xboole_0(X0,k2_tarski(sK3,sK3)) != X0
    | k2_mcart_1(sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5154,c_5092])).

cnf(c_5248,plain,
    ( k4_xboole_0(X0,k1_xboole_0) != X0
    | k2_mcart_1(sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_5092,c_5243])).

cnf(c_5249,plain,
    ( X0 != X0
    | k2_mcart_1(sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_5248,c_1])).

cnf(c_5250,plain,
    ( k2_mcart_1(sK3) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_5249])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_536,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1431,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | r1_tarski(k2_tarski(X0,X0),k2_tarski(k3_mcart_1(X1,X2,X0),k3_mcart_1(X1,X3,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_536])).

cnf(c_1830,plain,
    ( k2_tarski(k2_mcart_1(sK3),k2_mcart_1(sK3)) = k1_xboole_0
    | r1_tarski(k2_tarski(k2_mcart_1(sK3),k2_mcart_1(sK3)),k2_tarski(sK3,k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),X0,k2_mcart_1(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1431])).

cnf(c_1912,plain,
    ( k2_tarski(k2_mcart_1(sK3),k2_mcart_1(sK3)) = k1_xboole_0
    | r1_tarski(k2_tarski(k2_mcart_1(sK3),k2_mcart_1(sK3)),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1830])).

cnf(c_5589,plain,
    ( k2_tarski(sK3,sK3) = k1_xboole_0
    | r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5250,c_1912])).

cnf(c_6459,plain,
    ( k2_tarski(sK3,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5589,c_540])).

cnf(c_6480,plain,
    ( k4_xboole_0(X0,k2_tarski(sK3,sK3)) != X0
    | k3_xboole_0(X0,k1_xboole_0) != k2_tarski(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_6459,c_167])).

cnf(c_6504,plain,
    ( k4_xboole_0(X0,k1_xboole_0) != X0
    | k3_xboole_0(X0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6480,c_6459])).

cnf(c_6507,plain,
    ( X0 != X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6504,c_0,c_1])).

cnf(c_6508,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6507])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:41:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.24/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.01  
% 3.24/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.24/1.01  
% 3.24/1.01  ------  iProver source info
% 3.24/1.01  
% 3.24/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.24/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.24/1.01  git: non_committed_changes: false
% 3.24/1.01  git: last_make_outside_of_git: false
% 3.24/1.01  
% 3.24/1.01  ------ 
% 3.24/1.01  
% 3.24/1.01  ------ Input Options
% 3.24/1.01  
% 3.24/1.01  --out_options                           all
% 3.24/1.01  --tptp_safe_out                         true
% 3.24/1.01  --problem_path                          ""
% 3.24/1.01  --include_path                          ""
% 3.24/1.01  --clausifier                            res/vclausify_rel
% 3.24/1.01  --clausifier_options                    --mode clausify
% 3.24/1.01  --stdin                                 false
% 3.24/1.01  --stats_out                             all
% 3.24/1.01  
% 3.24/1.01  ------ General Options
% 3.24/1.01  
% 3.24/1.01  --fof                                   false
% 3.24/1.01  --time_out_real                         305.
% 3.24/1.01  --time_out_virtual                      -1.
% 3.24/1.01  --symbol_type_check                     false
% 3.24/1.01  --clausify_out                          false
% 3.24/1.01  --sig_cnt_out                           false
% 3.24/1.01  --trig_cnt_out                          false
% 3.24/1.01  --trig_cnt_out_tolerance                1.
% 3.24/1.01  --trig_cnt_out_sk_spl                   false
% 3.24/1.01  --abstr_cl_out                          false
% 3.24/1.01  
% 3.24/1.01  ------ Global Options
% 3.24/1.01  
% 3.24/1.01  --schedule                              default
% 3.24/1.01  --add_important_lit                     false
% 3.24/1.01  --prop_solver_per_cl                    1000
% 3.24/1.01  --min_unsat_core                        false
% 3.24/1.01  --soft_assumptions                      false
% 3.24/1.01  --soft_lemma_size                       3
% 3.24/1.01  --prop_impl_unit_size                   0
% 3.24/1.01  --prop_impl_unit                        []
% 3.24/1.01  --share_sel_clauses                     true
% 3.24/1.01  --reset_solvers                         false
% 3.24/1.01  --bc_imp_inh                            [conj_cone]
% 3.24/1.01  --conj_cone_tolerance                   3.
% 3.24/1.01  --extra_neg_conj                        none
% 3.24/1.01  --large_theory_mode                     true
% 3.24/1.01  --prolific_symb_bound                   200
% 3.24/1.01  --lt_threshold                          2000
% 3.24/1.01  --clause_weak_htbl                      true
% 3.24/1.01  --gc_record_bc_elim                     false
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing Options
% 3.24/1.01  
% 3.24/1.01  --preprocessing_flag                    true
% 3.24/1.01  --time_out_prep_mult                    0.1
% 3.24/1.01  --splitting_mode                        input
% 3.24/1.01  --splitting_grd                         true
% 3.24/1.01  --splitting_cvd                         false
% 3.24/1.01  --splitting_cvd_svl                     false
% 3.24/1.01  --splitting_nvd                         32
% 3.24/1.01  --sub_typing                            true
% 3.24/1.01  --prep_gs_sim                           true
% 3.24/1.01  --prep_unflatten                        true
% 3.24/1.01  --prep_res_sim                          true
% 3.24/1.01  --prep_upred                            true
% 3.24/1.01  --prep_sem_filter                       exhaustive
% 3.24/1.01  --prep_sem_filter_out                   false
% 3.24/1.01  --pred_elim                             true
% 3.24/1.01  --res_sim_input                         true
% 3.24/1.01  --eq_ax_congr_red                       true
% 3.24/1.01  --pure_diseq_elim                       true
% 3.24/1.01  --brand_transform                       false
% 3.24/1.01  --non_eq_to_eq                          false
% 3.24/1.01  --prep_def_merge                        true
% 3.24/1.01  --prep_def_merge_prop_impl              false
% 3.24/1.01  --prep_def_merge_mbd                    true
% 3.24/1.01  --prep_def_merge_tr_red                 false
% 3.24/1.01  --prep_def_merge_tr_cl                  false
% 3.24/1.01  --smt_preprocessing                     true
% 3.24/1.01  --smt_ac_axioms                         fast
% 3.24/1.01  --preprocessed_out                      false
% 3.24/1.01  --preprocessed_stats                    false
% 3.24/1.01  
% 3.24/1.01  ------ Abstraction refinement Options
% 3.24/1.01  
% 3.24/1.01  --abstr_ref                             []
% 3.24/1.01  --abstr_ref_prep                        false
% 3.24/1.01  --abstr_ref_until_sat                   false
% 3.24/1.01  --abstr_ref_sig_restrict                funpre
% 3.24/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.01  --abstr_ref_under                       []
% 3.24/1.01  
% 3.24/1.01  ------ SAT Options
% 3.24/1.01  
% 3.24/1.01  --sat_mode                              false
% 3.24/1.01  --sat_fm_restart_options                ""
% 3.24/1.01  --sat_gr_def                            false
% 3.24/1.01  --sat_epr_types                         true
% 3.24/1.01  --sat_non_cyclic_types                  false
% 3.24/1.01  --sat_finite_models                     false
% 3.24/1.01  --sat_fm_lemmas                         false
% 3.24/1.01  --sat_fm_prep                           false
% 3.24/1.01  --sat_fm_uc_incr                        true
% 3.24/1.01  --sat_out_model                         small
% 3.24/1.01  --sat_out_clauses                       false
% 3.24/1.01  
% 3.24/1.01  ------ QBF Options
% 3.24/1.01  
% 3.24/1.01  --qbf_mode                              false
% 3.24/1.01  --qbf_elim_univ                         false
% 3.24/1.01  --qbf_dom_inst                          none
% 3.24/1.01  --qbf_dom_pre_inst                      false
% 3.24/1.01  --qbf_sk_in                             false
% 3.24/1.01  --qbf_pred_elim                         true
% 3.24/1.01  --qbf_split                             512
% 3.24/1.01  
% 3.24/1.01  ------ BMC1 Options
% 3.24/1.01  
% 3.24/1.01  --bmc1_incremental                      false
% 3.24/1.01  --bmc1_axioms                           reachable_all
% 3.24/1.01  --bmc1_min_bound                        0
% 3.24/1.01  --bmc1_max_bound                        -1
% 3.24/1.01  --bmc1_max_bound_default                -1
% 3.24/1.01  --bmc1_symbol_reachability              true
% 3.24/1.01  --bmc1_property_lemmas                  false
% 3.24/1.01  --bmc1_k_induction                      false
% 3.24/1.01  --bmc1_non_equiv_states                 false
% 3.24/1.01  --bmc1_deadlock                         false
% 3.24/1.01  --bmc1_ucm                              false
% 3.24/1.01  --bmc1_add_unsat_core                   none
% 3.24/1.01  --bmc1_unsat_core_children              false
% 3.24/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.01  --bmc1_out_stat                         full
% 3.24/1.01  --bmc1_ground_init                      false
% 3.24/1.01  --bmc1_pre_inst_next_state              false
% 3.24/1.01  --bmc1_pre_inst_state                   false
% 3.24/1.01  --bmc1_pre_inst_reach_state             false
% 3.24/1.01  --bmc1_out_unsat_core                   false
% 3.24/1.01  --bmc1_aig_witness_out                  false
% 3.24/1.01  --bmc1_verbose                          false
% 3.24/1.01  --bmc1_dump_clauses_tptp                false
% 3.24/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.01  --bmc1_dump_file                        -
% 3.24/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.01  --bmc1_ucm_extend_mode                  1
% 3.24/1.01  --bmc1_ucm_init_mode                    2
% 3.24/1.01  --bmc1_ucm_cone_mode                    none
% 3.24/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.01  --bmc1_ucm_relax_model                  4
% 3.24/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.01  --bmc1_ucm_layered_model                none
% 3.24/1.01  --bmc1_ucm_max_lemma_size               10
% 3.24/1.01  
% 3.24/1.01  ------ AIG Options
% 3.24/1.01  
% 3.24/1.01  --aig_mode                              false
% 3.24/1.01  
% 3.24/1.01  ------ Instantiation Options
% 3.24/1.01  
% 3.24/1.01  --instantiation_flag                    true
% 3.24/1.01  --inst_sos_flag                         false
% 3.24/1.01  --inst_sos_phase                        true
% 3.24/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.01  --inst_lit_sel_side                     num_symb
% 3.24/1.01  --inst_solver_per_active                1400
% 3.24/1.01  --inst_solver_calls_frac                1.
% 3.24/1.01  --inst_passive_queue_type               priority_queues
% 3.24/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.01  --inst_passive_queues_freq              [25;2]
% 3.24/1.01  --inst_dismatching                      true
% 3.24/1.01  --inst_eager_unprocessed_to_passive     true
% 3.24/1.01  --inst_prop_sim_given                   true
% 3.24/1.01  --inst_prop_sim_new                     false
% 3.24/1.01  --inst_subs_new                         false
% 3.24/1.01  --inst_eq_res_simp                      false
% 3.24/1.01  --inst_subs_given                       false
% 3.24/1.01  --inst_orphan_elimination               true
% 3.24/1.01  --inst_learning_loop_flag               true
% 3.24/1.01  --inst_learning_start                   3000
% 3.24/1.01  --inst_learning_factor                  2
% 3.24/1.01  --inst_start_prop_sim_after_learn       3
% 3.24/1.01  --inst_sel_renew                        solver
% 3.24/1.01  --inst_lit_activity_flag                true
% 3.24/1.01  --inst_restr_to_given                   false
% 3.24/1.01  --inst_activity_threshold               500
% 3.24/1.01  --inst_out_proof                        true
% 3.24/1.01  
% 3.24/1.01  ------ Resolution Options
% 3.24/1.01  
% 3.24/1.01  --resolution_flag                       true
% 3.24/1.01  --res_lit_sel                           adaptive
% 3.24/1.01  --res_lit_sel_side                      none
% 3.24/1.01  --res_ordering                          kbo
% 3.24/1.01  --res_to_prop_solver                    active
% 3.24/1.01  --res_prop_simpl_new                    false
% 3.24/1.01  --res_prop_simpl_given                  true
% 3.24/1.01  --res_passive_queue_type                priority_queues
% 3.24/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.01  --res_passive_queues_freq               [15;5]
% 3.24/1.01  --res_forward_subs                      full
% 3.24/1.01  --res_backward_subs                     full
% 3.24/1.01  --res_forward_subs_resolution           true
% 3.24/1.01  --res_backward_subs_resolution          true
% 3.24/1.01  --res_orphan_elimination                true
% 3.24/1.01  --res_time_limit                        2.
% 3.24/1.01  --res_out_proof                         true
% 3.24/1.01  
% 3.24/1.01  ------ Superposition Options
% 3.24/1.01  
% 3.24/1.01  --superposition_flag                    true
% 3.24/1.01  --sup_passive_queue_type                priority_queues
% 3.24/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.01  --demod_completeness_check              fast
% 3.24/1.01  --demod_use_ground                      true
% 3.24/1.01  --sup_to_prop_solver                    passive
% 3.24/1.01  --sup_prop_simpl_new                    true
% 3.24/1.01  --sup_prop_simpl_given                  true
% 3.24/1.01  --sup_fun_splitting                     false
% 3.24/1.01  --sup_smt_interval                      50000
% 3.24/1.01  
% 3.24/1.01  ------ Superposition Simplification Setup
% 3.24/1.01  
% 3.24/1.01  --sup_indices_passive                   []
% 3.24/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_full_bw                           [BwDemod]
% 3.24/1.01  --sup_immed_triv                        [TrivRules]
% 3.24/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_immed_bw_main                     []
% 3.24/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.01  
% 3.24/1.01  ------ Combination Options
% 3.24/1.01  
% 3.24/1.01  --comb_res_mult                         3
% 3.24/1.01  --comb_sup_mult                         2
% 3.24/1.01  --comb_inst_mult                        10
% 3.24/1.01  
% 3.24/1.01  ------ Debug Options
% 3.24/1.01  
% 3.24/1.01  --dbg_backtrace                         false
% 3.24/1.01  --dbg_dump_prop_clauses                 false
% 3.24/1.01  --dbg_dump_prop_clauses_file            -
% 3.24/1.01  --dbg_out_stat                          false
% 3.24/1.01  ------ Parsing...
% 3.24/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.24/1.01  ------ Proving...
% 3.24/1.01  ------ Problem Properties 
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  clauses                                 18
% 3.24/1.01  conjectures                             4
% 3.24/1.01  EPR                                     3
% 3.24/1.01  Horn                                    12
% 3.24/1.01  unary                                   8
% 3.24/1.01  binary                                  4
% 3.24/1.01  lits                                    42
% 3.24/1.01  lits eq                                 36
% 3.24/1.01  fd_pure                                 0
% 3.24/1.01  fd_pseudo                               0
% 3.24/1.01  fd_cond                                 7
% 3.24/1.01  fd_pseudo_cond                          1
% 3.24/1.01  AC symbols                              0
% 3.24/1.01  
% 3.24/1.01  ------ Schedule dynamic 5 is on 
% 3.24/1.01  
% 3.24/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  ------ 
% 3.24/1.01  Current options:
% 3.24/1.01  ------ 
% 3.24/1.01  
% 3.24/1.01  ------ Input Options
% 3.24/1.01  
% 3.24/1.01  --out_options                           all
% 3.24/1.01  --tptp_safe_out                         true
% 3.24/1.01  --problem_path                          ""
% 3.24/1.01  --include_path                          ""
% 3.24/1.01  --clausifier                            res/vclausify_rel
% 3.24/1.01  --clausifier_options                    --mode clausify
% 3.24/1.01  --stdin                                 false
% 3.24/1.01  --stats_out                             all
% 3.24/1.01  
% 3.24/1.01  ------ General Options
% 3.24/1.01  
% 3.24/1.01  --fof                                   false
% 3.24/1.01  --time_out_real                         305.
% 3.24/1.01  --time_out_virtual                      -1.
% 3.24/1.01  --symbol_type_check                     false
% 3.24/1.01  --clausify_out                          false
% 3.24/1.01  --sig_cnt_out                           false
% 3.24/1.01  --trig_cnt_out                          false
% 3.24/1.01  --trig_cnt_out_tolerance                1.
% 3.24/1.01  --trig_cnt_out_sk_spl                   false
% 3.24/1.01  --abstr_cl_out                          false
% 3.24/1.01  
% 3.24/1.01  ------ Global Options
% 3.24/1.01  
% 3.24/1.01  --schedule                              default
% 3.24/1.01  --add_important_lit                     false
% 3.24/1.01  --prop_solver_per_cl                    1000
% 3.24/1.01  --min_unsat_core                        false
% 3.24/1.01  --soft_assumptions                      false
% 3.24/1.01  --soft_lemma_size                       3
% 3.24/1.01  --prop_impl_unit_size                   0
% 3.24/1.01  --prop_impl_unit                        []
% 3.24/1.01  --share_sel_clauses                     true
% 3.24/1.01  --reset_solvers                         false
% 3.24/1.01  --bc_imp_inh                            [conj_cone]
% 3.24/1.01  --conj_cone_tolerance                   3.
% 3.24/1.01  --extra_neg_conj                        none
% 3.24/1.01  --large_theory_mode                     true
% 3.24/1.01  --prolific_symb_bound                   200
% 3.24/1.01  --lt_threshold                          2000
% 3.24/1.01  --clause_weak_htbl                      true
% 3.24/1.01  --gc_record_bc_elim                     false
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing Options
% 3.24/1.01  
% 3.24/1.01  --preprocessing_flag                    true
% 3.24/1.01  --time_out_prep_mult                    0.1
% 3.24/1.01  --splitting_mode                        input
% 3.24/1.01  --splitting_grd                         true
% 3.24/1.01  --splitting_cvd                         false
% 3.24/1.01  --splitting_cvd_svl                     false
% 3.24/1.01  --splitting_nvd                         32
% 3.24/1.01  --sub_typing                            true
% 3.24/1.01  --prep_gs_sim                           true
% 3.24/1.01  --prep_unflatten                        true
% 3.24/1.01  --prep_res_sim                          true
% 3.24/1.01  --prep_upred                            true
% 3.24/1.01  --prep_sem_filter                       exhaustive
% 3.24/1.01  --prep_sem_filter_out                   false
% 3.24/1.01  --pred_elim                             true
% 3.24/1.01  --res_sim_input                         true
% 3.24/1.01  --eq_ax_congr_red                       true
% 3.24/1.01  --pure_diseq_elim                       true
% 3.24/1.01  --brand_transform                       false
% 3.24/1.01  --non_eq_to_eq                          false
% 3.24/1.01  --prep_def_merge                        true
% 3.24/1.01  --prep_def_merge_prop_impl              false
% 3.24/1.01  --prep_def_merge_mbd                    true
% 3.24/1.01  --prep_def_merge_tr_red                 false
% 3.24/1.01  --prep_def_merge_tr_cl                  false
% 3.24/1.01  --smt_preprocessing                     true
% 3.24/1.01  --smt_ac_axioms                         fast
% 3.24/1.01  --preprocessed_out                      false
% 3.24/1.01  --preprocessed_stats                    false
% 3.24/1.01  
% 3.24/1.01  ------ Abstraction refinement Options
% 3.24/1.01  
% 3.24/1.01  --abstr_ref                             []
% 3.24/1.01  --abstr_ref_prep                        false
% 3.24/1.01  --abstr_ref_until_sat                   false
% 3.24/1.01  --abstr_ref_sig_restrict                funpre
% 3.24/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.24/1.01  --abstr_ref_under                       []
% 3.24/1.01  
% 3.24/1.01  ------ SAT Options
% 3.24/1.01  
% 3.24/1.01  --sat_mode                              false
% 3.24/1.01  --sat_fm_restart_options                ""
% 3.24/1.01  --sat_gr_def                            false
% 3.24/1.01  --sat_epr_types                         true
% 3.24/1.01  --sat_non_cyclic_types                  false
% 3.24/1.01  --sat_finite_models                     false
% 3.24/1.01  --sat_fm_lemmas                         false
% 3.24/1.01  --sat_fm_prep                           false
% 3.24/1.01  --sat_fm_uc_incr                        true
% 3.24/1.01  --sat_out_model                         small
% 3.24/1.01  --sat_out_clauses                       false
% 3.24/1.01  
% 3.24/1.01  ------ QBF Options
% 3.24/1.01  
% 3.24/1.01  --qbf_mode                              false
% 3.24/1.01  --qbf_elim_univ                         false
% 3.24/1.01  --qbf_dom_inst                          none
% 3.24/1.01  --qbf_dom_pre_inst                      false
% 3.24/1.01  --qbf_sk_in                             false
% 3.24/1.01  --qbf_pred_elim                         true
% 3.24/1.01  --qbf_split                             512
% 3.24/1.01  
% 3.24/1.01  ------ BMC1 Options
% 3.24/1.01  
% 3.24/1.01  --bmc1_incremental                      false
% 3.24/1.01  --bmc1_axioms                           reachable_all
% 3.24/1.01  --bmc1_min_bound                        0
% 3.24/1.01  --bmc1_max_bound                        -1
% 3.24/1.01  --bmc1_max_bound_default                -1
% 3.24/1.01  --bmc1_symbol_reachability              true
% 3.24/1.01  --bmc1_property_lemmas                  false
% 3.24/1.01  --bmc1_k_induction                      false
% 3.24/1.01  --bmc1_non_equiv_states                 false
% 3.24/1.01  --bmc1_deadlock                         false
% 3.24/1.01  --bmc1_ucm                              false
% 3.24/1.01  --bmc1_add_unsat_core                   none
% 3.24/1.01  --bmc1_unsat_core_children              false
% 3.24/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.24/1.01  --bmc1_out_stat                         full
% 3.24/1.01  --bmc1_ground_init                      false
% 3.24/1.01  --bmc1_pre_inst_next_state              false
% 3.24/1.01  --bmc1_pre_inst_state                   false
% 3.24/1.01  --bmc1_pre_inst_reach_state             false
% 3.24/1.01  --bmc1_out_unsat_core                   false
% 3.24/1.01  --bmc1_aig_witness_out                  false
% 3.24/1.01  --bmc1_verbose                          false
% 3.24/1.01  --bmc1_dump_clauses_tptp                false
% 3.24/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.24/1.01  --bmc1_dump_file                        -
% 3.24/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.24/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.24/1.01  --bmc1_ucm_extend_mode                  1
% 3.24/1.01  --bmc1_ucm_init_mode                    2
% 3.24/1.01  --bmc1_ucm_cone_mode                    none
% 3.24/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.24/1.01  --bmc1_ucm_relax_model                  4
% 3.24/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.24/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.24/1.01  --bmc1_ucm_layered_model                none
% 3.24/1.01  --bmc1_ucm_max_lemma_size               10
% 3.24/1.01  
% 3.24/1.01  ------ AIG Options
% 3.24/1.01  
% 3.24/1.01  --aig_mode                              false
% 3.24/1.01  
% 3.24/1.01  ------ Instantiation Options
% 3.24/1.01  
% 3.24/1.01  --instantiation_flag                    true
% 3.24/1.01  --inst_sos_flag                         false
% 3.24/1.01  --inst_sos_phase                        true
% 3.24/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.24/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.24/1.01  --inst_lit_sel_side                     none
% 3.24/1.01  --inst_solver_per_active                1400
% 3.24/1.01  --inst_solver_calls_frac                1.
% 3.24/1.01  --inst_passive_queue_type               priority_queues
% 3.24/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.24/1.01  --inst_passive_queues_freq              [25;2]
% 3.24/1.01  --inst_dismatching                      true
% 3.24/1.01  --inst_eager_unprocessed_to_passive     true
% 3.24/1.01  --inst_prop_sim_given                   true
% 3.24/1.01  --inst_prop_sim_new                     false
% 3.24/1.01  --inst_subs_new                         false
% 3.24/1.01  --inst_eq_res_simp                      false
% 3.24/1.01  --inst_subs_given                       false
% 3.24/1.01  --inst_orphan_elimination               true
% 3.24/1.01  --inst_learning_loop_flag               true
% 3.24/1.01  --inst_learning_start                   3000
% 3.24/1.01  --inst_learning_factor                  2
% 3.24/1.01  --inst_start_prop_sim_after_learn       3
% 3.24/1.01  --inst_sel_renew                        solver
% 3.24/1.01  --inst_lit_activity_flag                true
% 3.24/1.01  --inst_restr_to_given                   false
% 3.24/1.01  --inst_activity_threshold               500
% 3.24/1.01  --inst_out_proof                        true
% 3.24/1.01  
% 3.24/1.01  ------ Resolution Options
% 3.24/1.01  
% 3.24/1.01  --resolution_flag                       false
% 3.24/1.01  --res_lit_sel                           adaptive
% 3.24/1.01  --res_lit_sel_side                      none
% 3.24/1.01  --res_ordering                          kbo
% 3.24/1.01  --res_to_prop_solver                    active
% 3.24/1.01  --res_prop_simpl_new                    false
% 3.24/1.01  --res_prop_simpl_given                  true
% 3.24/1.01  --res_passive_queue_type                priority_queues
% 3.24/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.24/1.01  --res_passive_queues_freq               [15;5]
% 3.24/1.01  --res_forward_subs                      full
% 3.24/1.01  --res_backward_subs                     full
% 3.24/1.01  --res_forward_subs_resolution           true
% 3.24/1.01  --res_backward_subs_resolution          true
% 3.24/1.01  --res_orphan_elimination                true
% 3.24/1.01  --res_time_limit                        2.
% 3.24/1.01  --res_out_proof                         true
% 3.24/1.01  
% 3.24/1.01  ------ Superposition Options
% 3.24/1.01  
% 3.24/1.01  --superposition_flag                    true
% 3.24/1.01  --sup_passive_queue_type                priority_queues
% 3.24/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.24/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.24/1.01  --demod_completeness_check              fast
% 3.24/1.01  --demod_use_ground                      true
% 3.24/1.01  --sup_to_prop_solver                    passive
% 3.24/1.01  --sup_prop_simpl_new                    true
% 3.24/1.01  --sup_prop_simpl_given                  true
% 3.24/1.01  --sup_fun_splitting                     false
% 3.24/1.01  --sup_smt_interval                      50000
% 3.24/1.01  
% 3.24/1.01  ------ Superposition Simplification Setup
% 3.24/1.01  
% 3.24/1.01  --sup_indices_passive                   []
% 3.24/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.24/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.24/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_full_bw                           [BwDemod]
% 3.24/1.01  --sup_immed_triv                        [TrivRules]
% 3.24/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.24/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_immed_bw_main                     []
% 3.24/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.24/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.24/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.24/1.01  
% 3.24/1.01  ------ Combination Options
% 3.24/1.01  
% 3.24/1.01  --comb_res_mult                         3
% 3.24/1.01  --comb_sup_mult                         2
% 3.24/1.01  --comb_inst_mult                        10
% 3.24/1.01  
% 3.24/1.01  ------ Debug Options
% 3.24/1.01  
% 3.24/1.01  --dbg_backtrace                         false
% 3.24/1.01  --dbg_dump_prop_clauses                 false
% 3.24/1.01  --dbg_dump_prop_clauses_file            -
% 3.24/1.01  --dbg_out_stat                          false
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  ------ Proving...
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  % SZS status Theorem for theBenchmark.p
% 3.24/1.01  
% 3.24/1.01   Resolution empty clause
% 3.24/1.01  
% 3.24/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.24/1.01  
% 3.24/1.01  fof(f11,conjecture,(
% 3.24/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f12,negated_conjecture,(
% 3.24/1.01    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.24/1.01    inference(negated_conjecture,[],[f11])).
% 3.24/1.01  
% 3.24/1.01  fof(f19,plain,(
% 3.24/1.01    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.24/1.01    inference(ennf_transformation,[],[f12])).
% 3.24/1.01  
% 3.24/1.01  fof(f23,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => ((k7_mcart_1(X0,X1,X2,sK3) = sK3 | k6_mcart_1(X0,X1,X2,sK3) = sK3 | k5_mcart_1(X0,X1,X2,sK3) = sK3) & m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2)))) )),
% 3.24/1.01    introduced(choice_axiom,[])).
% 3.24/1.01  
% 3.24/1.01  fof(f22,plain,(
% 3.24/1.01    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK0,sK1,sK2,X3) = X3 | k6_mcart_1(sK0,sK1,sK2,X3) = X3 | k5_mcart_1(sK0,sK1,sK2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 3.24/1.01    introduced(choice_axiom,[])).
% 3.24/1.01  
% 3.24/1.01  fof(f24,plain,(
% 3.24/1.01    ((k7_mcart_1(sK0,sK1,sK2,sK3) = sK3 | k6_mcart_1(sK0,sK1,sK2,sK3) = sK3 | k5_mcart_1(sK0,sK1,sK2,sK3) = sK3) & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 3.24/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f23,f22])).
% 3.24/1.01  
% 3.24/1.01  fof(f45,plain,(
% 3.24/1.01    k7_mcart_1(sK0,sK1,sK2,sK3) = sK3 | k6_mcart_1(sK0,sK1,sK2,sK3) = sK3 | k5_mcart_1(sK0,sK1,sK2,sK3) = sK3),
% 3.24/1.01    inference(cnf_transformation,[],[f24])).
% 3.24/1.01  
% 3.24/1.01  fof(f10,axiom,(
% 3.24/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f18,plain,(
% 3.24/1.01    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.24/1.01    inference(ennf_transformation,[],[f10])).
% 3.24/1.01  
% 3.24/1.01  fof(f40,plain,(
% 3.24/1.01    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.24/1.01    inference(cnf_transformation,[],[f18])).
% 3.24/1.01  
% 3.24/1.01  fof(f44,plain,(
% 3.24/1.01    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 3.24/1.01    inference(cnf_transformation,[],[f24])).
% 3.24/1.01  
% 3.24/1.01  fof(f41,plain,(
% 3.24/1.01    k1_xboole_0 != sK0),
% 3.24/1.01    inference(cnf_transformation,[],[f24])).
% 3.24/1.01  
% 3.24/1.01  fof(f42,plain,(
% 3.24/1.01    k1_xboole_0 != sK1),
% 3.24/1.01    inference(cnf_transformation,[],[f24])).
% 3.24/1.01  
% 3.24/1.01  fof(f43,plain,(
% 3.24/1.01    k1_xboole_0 != sK2),
% 3.24/1.01    inference(cnf_transformation,[],[f24])).
% 3.24/1.01  
% 3.24/1.01  fof(f39,plain,(
% 3.24/1.01    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.24/1.01    inference(cnf_transformation,[],[f18])).
% 3.24/1.01  
% 3.24/1.01  fof(f38,plain,(
% 3.24/1.01    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.24/1.01    inference(cnf_transformation,[],[f18])).
% 3.24/1.01  
% 3.24/1.01  fof(f8,axiom,(
% 3.24/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f16,plain,(
% 3.24/1.01    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.24/1.01    inference(ennf_transformation,[],[f8])).
% 3.24/1.01  
% 3.24/1.01  fof(f34,plain,(
% 3.24/1.01    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.24/1.01    inference(cnf_transformation,[],[f16])).
% 3.24/1.01  
% 3.24/1.01  fof(f7,axiom,(
% 3.24/1.01    ! [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f33,plain,(
% 3.24/1.01    ( ! [X2,X0,X3,X1] : (k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k1_tarski(X3))) )),
% 3.24/1.01    inference(cnf_transformation,[],[f7])).
% 3.24/1.01  
% 3.24/1.01  fof(f3,axiom,(
% 3.24/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f27,plain,(
% 3.24/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f3])).
% 3.24/1.01  
% 3.24/1.01  fof(f51,plain,(
% 3.24/1.01    ( ! [X2,X0,X3,X1] : (k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) = k3_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2),k2_tarski(X3,X3))) )),
% 3.24/1.01    inference(definition_unfolding,[],[f33,f27,f27])).
% 3.24/1.01  
% 3.24/1.01  fof(f9,axiom,(
% 3.24/1.01    ! [X0,X1,X2] : (~(~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))) => k1_xboole_0 = X0)),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f17,plain,(
% 3.24/1.01    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))))),
% 3.24/1.01    inference(ennf_transformation,[],[f9])).
% 3.24/1.01  
% 3.24/1.01  fof(f35,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))) )),
% 3.24/1.01    inference(cnf_transformation,[],[f17])).
% 3.24/1.01  
% 3.24/1.01  fof(f5,axiom,(
% 3.24/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f20,plain,(
% 3.24/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.24/1.01    inference(nnf_transformation,[],[f5])).
% 3.24/1.01  
% 3.24/1.01  fof(f21,plain,(
% 3.24/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.24/1.01    inference(flattening,[],[f20])).
% 3.24/1.01  
% 3.24/1.01  fof(f31,plain,(
% 3.24/1.01    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 3.24/1.01    inference(cnf_transformation,[],[f21])).
% 3.24/1.01  
% 3.24/1.01  fof(f47,plain,(
% 3.24/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_tarski(X1,X1)) | k2_tarski(X1,X1) != X0) )),
% 3.24/1.01    inference(definition_unfolding,[],[f31,f27,f27])).
% 3.24/1.01  
% 3.24/1.01  fof(f52,plain,(
% 3.24/1.01    ( ! [X1] : (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 3.24/1.01    inference(equality_resolution,[],[f47])).
% 3.24/1.01  
% 3.24/1.01  fof(f4,axiom,(
% 3.24/1.01    ! [X0,X1] : (k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) => r2_hidden(X1,X0))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f14,plain,(
% 3.24/1.01    ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1))),
% 3.24/1.01    inference(ennf_transformation,[],[f4])).
% 3.24/1.01  
% 3.24/1.01  fof(f28,plain,(
% 3.24/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f14])).
% 3.24/1.01  
% 3.24/1.01  fof(f46,plain,(
% 3.24/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k2_tarski(X1,X1)) != k2_tarski(X1,X1)) )),
% 3.24/1.01    inference(definition_unfolding,[],[f28,f27,f27])).
% 3.24/1.01  
% 3.24/1.01  fof(f6,axiom,(
% 3.24/1.01    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f13,plain,(
% 3.24/1.01    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 => ~r2_hidden(X1,X0))),
% 3.24/1.01    inference(unused_predicate_definition_removal,[],[f6])).
% 3.24/1.01  
% 3.24/1.01  fof(f15,plain,(
% 3.24/1.01    ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0)),
% 3.24/1.01    inference(ennf_transformation,[],[f13])).
% 3.24/1.01  
% 3.24/1.01  fof(f32,plain,(
% 3.24/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 3.24/1.01    inference(cnf_transformation,[],[f15])).
% 3.24/1.01  
% 3.24/1.01  fof(f50,plain,(
% 3.24/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0) )),
% 3.24/1.01    inference(definition_unfolding,[],[f32,f27])).
% 3.24/1.01  
% 3.24/1.01  fof(f1,axiom,(
% 3.24/1.01    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f25,plain,(
% 3.24/1.01    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.24/1.01    inference(cnf_transformation,[],[f1])).
% 3.24/1.01  
% 3.24/1.01  fof(f2,axiom,(
% 3.24/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.24/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.24/1.01  
% 3.24/1.01  fof(f26,plain,(
% 3.24/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.24/1.01    inference(cnf_transformation,[],[f2])).
% 3.24/1.01  
% 3.24/1.01  fof(f37,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))) )),
% 3.24/1.01    inference(cnf_transformation,[],[f17])).
% 3.24/1.01  
% 3.24/1.01  fof(f36,plain,(
% 3.24/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))) )),
% 3.24/1.01    inference(cnf_transformation,[],[f17])).
% 3.24/1.01  
% 3.24/1.01  cnf(c_15,negated_conjecture,
% 3.24/1.01      ( k7_mcart_1(sK0,sK1,sK2,sK3) = sK3
% 3.24/1.01      | k6_mcart_1(sK0,sK1,sK2,sK3) = sK3
% 3.24/1.01      | k5_mcart_1(sK0,sK1,sK2,sK3) = sK3 ),
% 3.24/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_12,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 3.24/1.01      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.24/1.01      | k1_xboole_0 = X1
% 3.24/1.01      | k1_xboole_0 = X3
% 3.24/1.01      | k1_xboole_0 = X2 ),
% 3.24/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_16,negated_conjecture,
% 3.24/1.01      ( m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
% 3.24/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_256,plain,
% 3.24/1.01      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.24/1.01      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
% 3.24/1.01      | sK3 != X3
% 3.24/1.01      | k1_xboole_0 = X2
% 3.24/1.01      | k1_xboole_0 = X0
% 3.24/1.01      | k1_xboole_0 = X1 ),
% 3.24/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_257,plain,
% 3.24/1.01      ( k7_mcart_1(X0,X1,X2,sK3) = k2_mcart_1(sK3)
% 3.24/1.01      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
% 3.24/1.01      | k1_xboole_0 = X0
% 3.24/1.01      | k1_xboole_0 = X1
% 3.24/1.01      | k1_xboole_0 = X2 ),
% 3.24/1.01      inference(unflattening,[status(thm)],[c_256]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_737,plain,
% 3.24/1.01      ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
% 3.24/1.01      | sK2 = k1_xboole_0
% 3.24/1.01      | sK1 = k1_xboole_0
% 3.24/1.01      | sK0 = k1_xboole_0 ),
% 3.24/1.01      inference(equality_resolution,[status(thm)],[c_257]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_19,negated_conjecture,
% 3.24/1.01      ( k1_xboole_0 != sK0 ),
% 3.24/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_18,negated_conjecture,
% 3.24/1.01      ( k1_xboole_0 != sK1 ),
% 3.24/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_17,negated_conjecture,
% 3.24/1.01      ( k1_xboole_0 != sK2 ),
% 3.24/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_406,plain,( X0 = X0 ),theory(equality) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_431,plain,
% 3.24/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_406]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_407,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_697,plain,
% 3.24/1.01      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_407]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_698,plain,
% 3.24/1.01      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_697]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_699,plain,
% 3.24/1.01      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_407]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_700,plain,
% 3.24/1.01      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_699]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_701,plain,
% 3.24/1.01      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_407]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_702,plain,
% 3.24/1.01      ( sK0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 != k1_xboole_0 ),
% 3.24/1.01      inference(instantiation,[status(thm)],[c_701]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1026,plain,
% 3.24/1.01      ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_737,c_19,c_18,c_17,c_431,c_698,c_700,c_702]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1029,plain,
% 3.24/1.01      ( k6_mcart_1(sK0,sK1,sK2,sK3) = sK3
% 3.24/1.01      | k5_mcart_1(sK0,sK1,sK2,sK3) = sK3
% 3.24/1.01      | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_15,c_1026]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_13,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 3.24/1.01      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.24/1.01      | k1_xboole_0 = X1
% 3.24/1.01      | k1_xboole_0 = X3
% 3.24/1.01      | k1_xboole_0 = X2 ),
% 3.24/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_238,plain,
% 3.24/1.01      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.24/1.01      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
% 3.24/1.01      | sK3 != X3
% 3.24/1.01      | k1_xboole_0 = X2
% 3.24/1.01      | k1_xboole_0 = X0
% 3.24/1.01      | k1_xboole_0 = X1 ),
% 3.24/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_239,plain,
% 3.24/1.01      ( k6_mcart_1(X0,X1,X2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
% 3.24/1.01      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
% 3.24/1.01      | k1_xboole_0 = X0
% 3.24/1.01      | k1_xboole_0 = X1
% 3.24/1.01      | k1_xboole_0 = X2 ),
% 3.24/1.01      inference(unflattening,[status(thm)],[c_238]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_750,plain,
% 3.24/1.01      ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
% 3.24/1.01      | sK2 = k1_xboole_0
% 3.24/1.01      | sK1 = k1_xboole_0
% 3.24/1.01      | sK0 = k1_xboole_0 ),
% 3.24/1.01      inference(equality_resolution,[status(thm)],[c_239]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1153,plain,
% 3.24/1.01      ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_750,c_19,c_18,c_17,c_431,c_698,c_700,c_702]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1156,plain,
% 3.24/1.01      ( k5_mcart_1(sK0,sK1,sK2,sK3) = sK3
% 3.24/1.01      | k2_mcart_1(k1_mcart_1(sK3)) = sK3
% 3.24/1.01      | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1029,c_1153]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_14,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 3.24/1.01      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.24/1.01      | k1_xboole_0 = X1
% 3.24/1.01      | k1_xboole_0 = X3
% 3.24/1.01      | k1_xboole_0 = X2 ),
% 3.24/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_220,plain,
% 3.24/1.01      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.24/1.01      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
% 3.24/1.01      | sK3 != X3
% 3.24/1.01      | k1_xboole_0 = X2
% 3.24/1.01      | k1_xboole_0 = X0
% 3.24/1.01      | k1_xboole_0 = X1 ),
% 3.24/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_16]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_221,plain,
% 3.24/1.01      ( k5_mcart_1(X0,X1,X2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
% 3.24/1.01      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
% 3.24/1.01      | k1_xboole_0 = X0
% 3.24/1.01      | k1_xboole_0 = X1
% 3.24/1.01      | k1_xboole_0 = X2 ),
% 3.24/1.01      inference(unflattening,[status(thm)],[c_220]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_743,plain,
% 3.24/1.01      ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
% 3.24/1.01      | sK2 = k1_xboole_0
% 3.24/1.01      | sK1 = k1_xboole_0
% 3.24/1.01      | sK0 = k1_xboole_0 ),
% 3.24/1.01      inference(equality_resolution,[status(thm)],[c_221]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1094,plain,
% 3.24/1.01      ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_743,c_19,c_18,c_17,c_431,c_698,c_700,c_702]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1158,plain,
% 3.24/1.01      ( k1_mcart_1(k1_mcart_1(sK3)) = sK3
% 3.24/1.01      | k2_mcart_1(k1_mcart_1(sK3)) = sK3
% 3.24/1.01      | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(demodulation,[status(thm)],[c_1156,c_1094]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_8,plain,
% 3.24/1.01      ( ~ m1_subset_1(X0,k3_zfmisc_1(X1,X2,X3))
% 3.24/1.01      | k3_mcart_1(k5_mcart_1(X1,X2,X3,X0),k6_mcart_1(X1,X2,X3,X0),k7_mcart_1(X1,X2,X3,X0)) = X0
% 3.24/1.01      | k1_xboole_0 = X1
% 3.24/1.01      | k1_xboole_0 = X3
% 3.24/1.01      | k1_xboole_0 = X2 ),
% 3.24/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_274,plain,
% 3.24/1.01      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
% 3.24/1.01      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
% 3.24/1.01      | sK3 != X3
% 3.24/1.01      | k1_xboole_0 = X2
% 3.24/1.01      | k1_xboole_0 = X0
% 3.24/1.01      | k1_xboole_0 = X1 ),
% 3.24/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_275,plain,
% 3.24/1.01      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
% 3.24/1.01      | k3_mcart_1(k5_mcart_1(X0,X1,X2,sK3),k6_mcart_1(X0,X1,X2,sK3),k7_mcart_1(X0,X1,X2,sK3)) = sK3
% 3.24/1.01      | k1_xboole_0 = X0
% 3.24/1.01      | k1_xboole_0 = X1
% 3.24/1.01      | k1_xboole_0 = X2 ),
% 3.24/1.01      inference(unflattening,[status(thm)],[c_274]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_756,plain,
% 3.24/1.01      ( k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) = sK3
% 3.24/1.01      | sK2 = k1_xboole_0
% 3.24/1.01      | sK1 = k1_xboole_0
% 3.24/1.01      | sK0 = k1_xboole_0 ),
% 3.24/1.01      inference(equality_resolution,[status(thm)],[c_275]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1159,plain,
% 3.24/1.01      ( k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) = sK3 ),
% 3.24/1.01      inference(global_propositional_subsumption,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_756,c_19,c_18,c_17,c_431,c_698,c_700,c_702]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1161,plain,
% 3.24/1.01      ( k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) = sK3 ),
% 3.24/1.01      inference(light_normalisation,
% 3.24/1.01                [status(thm)],
% 3.24/1.01                [c_1159,c_1026,c_1094,c_1153]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_7,plain,
% 3.24/1.01      ( k3_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2),k2_tarski(X3,X3)) = k2_tarski(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3)) ),
% 3.24/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_11,plain,
% 3.24/1.01      ( ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0 ),
% 3.24/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_535,plain,
% 3.24/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_902,plain,
% 3.24/1.01      ( k2_tarski(X0,X0) = k1_xboole_0
% 3.24/1.01      | r1_tarski(k2_tarski(X0,X0),k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X3,X2))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_7,c_535]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1811,plain,
% 3.24/1.01      ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) = k1_xboole_0
% 3.24/1.01      | r1_tarski(k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))),k2_tarski(sK3,k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),X0,k2_mcart_1(sK3)))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1161,c_902]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2161,plain,
% 3.24/1.01      ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) = k1_xboole_0
% 3.24/1.01      | r1_tarski(k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))),k2_tarski(sK3,sK3)) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1161,c_1811]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2202,plain,
% 3.24/1.01      ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) = k1_xboole_0
% 3.24/1.01      | k2_mcart_1(k1_mcart_1(sK3)) = sK3
% 3.24/1.01      | k2_mcart_1(sK3) = sK3
% 3.24/1.01      | r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1158,c_2161]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3,plain,
% 3.24/1.01      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X0)) ),
% 3.24/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_540,plain,
% 3.24/1.01      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X0)) = iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2863,plain,
% 3.24/1.01      ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) = k1_xboole_0
% 3.24/1.01      | k2_mcart_1(k1_mcart_1(sK3)) = sK3
% 3.24/1.01      | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_2202,c_540]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2,plain,
% 3.24/1.01      ( r2_hidden(X0,X1)
% 3.24/1.01      | k3_xboole_0(X1,k2_tarski(X0,X0)) != k2_tarski(X0,X0) ),
% 3.24/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6,plain,
% 3.24/1.01      ( ~ r2_hidden(X0,X1) | k4_xboole_0(X1,k2_tarski(X0,X0)) != X1 ),
% 3.24/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_167,plain,
% 3.24/1.01      ( k4_xboole_0(X0,k2_tarski(X1,X1)) != X0
% 3.24/1.01      | k3_xboole_0(X0,k2_tarski(X1,X1)) != k2_tarski(X1,X1) ),
% 3.24/1.01      inference(resolution,[status(thm)],[c_2,c_6]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2866,plain,
% 3.24/1.01      ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) != k3_xboole_0(X0,k1_xboole_0)
% 3.24/1.01      | k4_xboole_0(X0,k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3)))) != X0
% 3.24/1.01      | k2_mcart_1(k1_mcart_1(sK3)) = sK3
% 3.24/1.01      | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_2863,c_167]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_0,plain,
% 3.24/1.01      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.24/1.01      inference(cnf_transformation,[],[f25]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_2918,plain,
% 3.24/1.01      ( k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3))) != k1_xboole_0
% 3.24/1.01      | k4_xboole_0(X0,k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3)))) != X0
% 3.24/1.01      | k2_mcart_1(k1_mcart_1(sK3)) = sK3
% 3.24/1.01      | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(light_normalisation,[status(thm)],[c_2866,c_0]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3587,plain,
% 3.24/1.01      ( k4_xboole_0(X0,k2_tarski(k1_mcart_1(k1_mcart_1(sK3)),k1_mcart_1(k1_mcart_1(sK3)))) != X0
% 3.24/1.01      | k2_mcart_1(k1_mcart_1(sK3)) = sK3
% 3.24/1.01      | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2918,c_2863]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3593,plain,
% 3.24/1.01      ( k4_xboole_0(X0,k1_xboole_0) != X0
% 3.24/1.01      | k2_mcart_1(k1_mcart_1(sK3)) = sK3
% 3.24/1.01      | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_2863,c_3587]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1,plain,
% 3.24/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.24/1.01      inference(cnf_transformation,[],[f26]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3605,plain,
% 3.24/1.01      ( X0 != X0 | k2_mcart_1(k1_mcart_1(sK3)) = sK3 | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(light_normalisation,[status(thm)],[c_3593,c_1]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3606,plain,
% 3.24/1.01      ( k2_mcart_1(k1_mcart_1(sK3)) = sK3 | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(equality_resolution_simp,[status(thm)],[c_3605]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3760,plain,
% 3.24/1.01      ( k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),sK3,k2_mcart_1(sK3)) = sK3
% 3.24/1.01      | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_3606,c_1161]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_9,plain,
% 3.24/1.01      ( ~ r1_tarski(X0,k3_zfmisc_1(X1,X0,X2)) | k1_xboole_0 = X0 ),
% 3.24/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_537,plain,
% 3.24/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k3_zfmisc_1(X1,X0,X2)) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1468,plain,
% 3.24/1.01      ( k2_tarski(X0,X1) = k1_xboole_0
% 3.24/1.01      | r1_tarski(k2_tarski(X0,X1),k2_tarski(k3_mcart_1(X2,X0,X3),k3_mcart_1(X2,X1,X3))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_7,c_537]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_3819,plain,
% 3.24/1.01      ( k2_tarski(sK3,X0) = k1_xboole_0
% 3.24/1.01      | k2_mcart_1(sK3) = sK3
% 3.24/1.01      | r1_tarski(k2_tarski(sK3,X0),k2_tarski(sK3,k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),X0,k2_mcart_1(sK3)))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_3760,c_1468]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_4513,plain,
% 3.24/1.01      ( k2_tarski(sK3,sK3) = k1_xboole_0
% 3.24/1.01      | k2_mcart_1(sK3) = sK3
% 3.24/1.01      | r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_3760,c_3819]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5092,plain,
% 3.24/1.01      ( k2_tarski(sK3,sK3) = k1_xboole_0 | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4513,c_540]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5093,plain,
% 3.24/1.01      ( k4_xboole_0(X0,k2_tarski(sK3,sK3)) != X0
% 3.24/1.01      | k3_xboole_0(X0,k1_xboole_0) != k2_tarski(sK3,sK3)
% 3.24/1.01      | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_5092,c_167]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5154,plain,
% 3.24/1.01      ( k2_tarski(sK3,sK3) != k1_xboole_0
% 3.24/1.01      | k4_xboole_0(X0,k2_tarski(sK3,sK3)) != X0
% 3.24/1.01      | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(light_normalisation,[status(thm)],[c_5093,c_0]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5243,plain,
% 3.24/1.01      ( k4_xboole_0(X0,k2_tarski(sK3,sK3)) != X0 | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(global_propositional_subsumption,[status(thm)],[c_5154,c_5092]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5248,plain,
% 3.24/1.01      ( k4_xboole_0(X0,k1_xboole_0) != X0 | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_5092,c_5243]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5249,plain,
% 3.24/1.01      ( X0 != X0 | k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(light_normalisation,[status(thm)],[c_5248,c_1]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5250,plain,
% 3.24/1.01      ( k2_mcart_1(sK3) = sK3 ),
% 3.24/1.01      inference(equality_resolution_simp,[status(thm)],[c_5249]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_10,plain,
% 3.24/1.01      ( ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) | k1_xboole_0 = X0 ),
% 3.24/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_536,plain,
% 3.24/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) != iProver_top ),
% 3.24/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1431,plain,
% 3.24/1.01      ( k2_tarski(X0,X0) = k1_xboole_0
% 3.24/1.01      | r1_tarski(k2_tarski(X0,X0),k2_tarski(k3_mcart_1(X1,X2,X0),k3_mcart_1(X1,X3,X0))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_7,c_536]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1830,plain,
% 3.24/1.01      ( k2_tarski(k2_mcart_1(sK3),k2_mcart_1(sK3)) = k1_xboole_0
% 3.24/1.01      | r1_tarski(k2_tarski(k2_mcart_1(sK3),k2_mcart_1(sK3)),k2_tarski(sK3,k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),X0,k2_mcart_1(sK3)))) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1161,c_1431]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_1912,plain,
% 3.24/1.01      ( k2_tarski(k2_mcart_1(sK3),k2_mcart_1(sK3)) = k1_xboole_0
% 3.24/1.01      | r1_tarski(k2_tarski(k2_mcart_1(sK3),k2_mcart_1(sK3)),k2_tarski(sK3,sK3)) != iProver_top ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_1161,c_1830]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_5589,plain,
% 3.24/1.01      ( k2_tarski(sK3,sK3) = k1_xboole_0
% 3.24/1.01      | r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK3,sK3)) != iProver_top ),
% 3.24/1.01      inference(demodulation,[status(thm)],[c_5250,c_1912]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6459,plain,
% 3.24/1.01      ( k2_tarski(sK3,sK3) = k1_xboole_0 ),
% 3.24/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5589,c_540]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6480,plain,
% 3.24/1.01      ( k4_xboole_0(X0,k2_tarski(sK3,sK3)) != X0
% 3.24/1.01      | k3_xboole_0(X0,k1_xboole_0) != k2_tarski(sK3,sK3) ),
% 3.24/1.01      inference(superposition,[status(thm)],[c_6459,c_167]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6504,plain,
% 3.24/1.01      ( k4_xboole_0(X0,k1_xboole_0) != X0
% 3.24/1.01      | k3_xboole_0(X0,k1_xboole_0) != k1_xboole_0 ),
% 3.24/1.01      inference(light_normalisation,[status(thm)],[c_6480,c_6459]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6507,plain,
% 3.24/1.01      ( X0 != X0 | k1_xboole_0 != k1_xboole_0 ),
% 3.24/1.01      inference(light_normalisation,[status(thm)],[c_6504,c_0,c_1]) ).
% 3.24/1.01  
% 3.24/1.01  cnf(c_6508,plain,
% 3.24/1.01      ( $false ),
% 3.24/1.01      inference(equality_resolution_simp,[status(thm)],[c_6507]) ).
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.24/1.01  
% 3.24/1.01  ------                               Statistics
% 3.24/1.01  
% 3.24/1.01  ------ General
% 3.24/1.01  
% 3.24/1.01  abstr_ref_over_cycles:                  0
% 3.24/1.01  abstr_ref_under_cycles:                 0
% 3.24/1.01  gc_basic_clause_elim:                   0
% 3.24/1.01  forced_gc_time:                         0
% 3.24/1.01  parsing_time:                           0.008
% 3.24/1.01  unif_index_cands_time:                  0.
% 3.24/1.01  unif_index_add_time:                    0.
% 3.24/1.01  orderings_time:                         0.
% 3.24/1.01  out_proof_time:                         0.013
% 3.24/1.01  total_time:                             0.329
% 3.24/1.01  num_of_symbols:                         49
% 3.24/1.01  num_of_terms:                           8636
% 3.24/1.01  
% 3.24/1.01  ------ Preprocessing
% 3.24/1.01  
% 3.24/1.01  num_of_splits:                          0
% 3.24/1.01  num_of_split_atoms:                     0
% 3.24/1.01  num_of_reused_defs:                     0
% 3.24/1.01  num_eq_ax_congr_red:                    8
% 3.24/1.01  num_of_sem_filtered_clauses:            1
% 3.24/1.01  num_of_subtypes:                        0
% 3.24/1.01  monotx_restored_types:                  0
% 3.24/1.01  sat_num_of_epr_types:                   0
% 3.24/1.01  sat_num_of_non_cyclic_types:            0
% 3.24/1.01  sat_guarded_non_collapsed_types:        0
% 3.24/1.01  num_pure_diseq_elim:                    0
% 3.24/1.01  simp_replaced_by:                       0
% 3.24/1.01  res_preprocessed:                       101
% 3.24/1.01  prep_upred:                             0
% 3.24/1.01  prep_unflattend:                        20
% 3.24/1.01  smt_new_axioms:                         0
% 3.24/1.01  pred_elim_cands:                        1
% 3.24/1.01  pred_elim:                              2
% 3.24/1.01  pred_elim_cl:                           2
% 3.24/1.01  pred_elim_cycles:                       5
% 3.24/1.01  merged_defs:                            0
% 3.24/1.01  merged_defs_ncl:                        0
% 3.24/1.01  bin_hyper_res:                          0
% 3.24/1.01  prep_cycles:                            4
% 3.24/1.01  pred_elim_time:                         0.004
% 3.24/1.01  splitting_time:                         0.
% 3.24/1.01  sem_filter_time:                        0.
% 3.24/1.01  monotx_time:                            0.
% 3.24/1.01  subtype_inf_time:                       0.
% 3.24/1.01  
% 3.24/1.01  ------ Problem properties
% 3.24/1.01  
% 3.24/1.01  clauses:                                18
% 3.24/1.01  conjectures:                            4
% 3.24/1.01  epr:                                    3
% 3.24/1.01  horn:                                   12
% 3.24/1.01  ground:                                 4
% 3.24/1.01  unary:                                  8
% 3.24/1.01  binary:                                 4
% 3.24/1.01  lits:                                   42
% 3.24/1.01  lits_eq:                                36
% 3.24/1.01  fd_pure:                                0
% 3.24/1.01  fd_pseudo:                              0
% 3.24/1.01  fd_cond:                                7
% 3.24/1.01  fd_pseudo_cond:                         1
% 3.24/1.01  ac_symbols:                             0
% 3.24/1.01  
% 3.24/1.01  ------ Propositional Solver
% 3.24/1.01  
% 3.24/1.01  prop_solver_calls:                      29
% 3.24/1.01  prop_fast_solver_calls:                 1376
% 3.24/1.01  smt_solver_calls:                       0
% 3.24/1.01  smt_fast_solver_calls:                  0
% 3.24/1.01  prop_num_of_clauses:                    2257
% 3.24/1.01  prop_preprocess_simplified:             5483
% 3.24/1.01  prop_fo_subsumed:                       179
% 3.24/1.01  prop_solver_time:                       0.
% 3.24/1.01  smt_solver_time:                        0.
% 3.24/1.01  smt_fast_solver_time:                   0.
% 3.24/1.01  prop_fast_solver_time:                  0.
% 3.24/1.01  prop_unsat_core_time:                   0.
% 3.24/1.01  
% 3.24/1.01  ------ QBF
% 3.24/1.01  
% 3.24/1.01  qbf_q_res:                              0
% 3.24/1.01  qbf_num_tautologies:                    0
% 3.24/1.01  qbf_prep_cycles:                        0
% 3.24/1.01  
% 3.24/1.01  ------ BMC1
% 3.24/1.01  
% 3.24/1.01  bmc1_current_bound:                     -1
% 3.24/1.01  bmc1_last_solved_bound:                 -1
% 3.24/1.01  bmc1_unsat_core_size:                   -1
% 3.24/1.01  bmc1_unsat_core_parents_size:           -1
% 3.24/1.01  bmc1_merge_next_fun:                    0
% 3.24/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.24/1.01  
% 3.24/1.01  ------ Instantiation
% 3.24/1.01  
% 3.24/1.01  inst_num_of_clauses:                    1071
% 3.24/1.01  inst_num_in_passive:                    23
% 3.24/1.01  inst_num_in_active:                     547
% 3.24/1.01  inst_num_in_unprocessed:                501
% 3.24/1.01  inst_num_of_loops:                      550
% 3.24/1.01  inst_num_of_learning_restarts:          0
% 3.24/1.01  inst_num_moves_active_passive:          1
% 3.24/1.01  inst_lit_activity:                      0
% 3.24/1.01  inst_lit_activity_moves:                0
% 3.24/1.01  inst_num_tautologies:                   0
% 3.24/1.01  inst_num_prop_implied:                  0
% 3.24/1.01  inst_num_existing_simplified:           0
% 3.24/1.01  inst_num_eq_res_simplified:             0
% 3.24/1.01  inst_num_child_elim:                    0
% 3.24/1.01  inst_num_of_dismatching_blockings:      250
% 3.24/1.01  inst_num_of_non_proper_insts:           997
% 3.24/1.01  inst_num_of_duplicates:                 0
% 3.24/1.01  inst_inst_num_from_inst_to_res:         0
% 3.24/1.01  inst_dismatching_checking_time:         0.
% 3.24/1.01  
% 3.24/1.01  ------ Resolution
% 3.24/1.01  
% 3.24/1.01  res_num_of_clauses:                     0
% 3.24/1.01  res_num_in_passive:                     0
% 3.24/1.01  res_num_in_active:                      0
% 3.24/1.01  res_num_of_loops:                       105
% 3.24/1.01  res_forward_subset_subsumed:            19
% 3.24/1.01  res_backward_subset_subsumed:           0
% 3.24/1.01  res_forward_subsumed:                   0
% 3.24/1.01  res_backward_subsumed:                  0
% 3.24/1.01  res_forward_subsumption_resolution:     0
% 3.24/1.01  res_backward_subsumption_resolution:    0
% 3.24/1.01  res_clause_to_clause_subsumption:       685
% 3.24/1.01  res_orphan_elimination:                 0
% 3.24/1.01  res_tautology_del:                      35
% 3.24/1.01  res_num_eq_res_simplified:              0
% 3.24/1.01  res_num_sel_changes:                    0
% 3.24/1.01  res_moves_from_active_to_pass:          0
% 3.24/1.01  
% 3.24/1.01  ------ Superposition
% 3.24/1.01  
% 3.24/1.01  sup_time_total:                         0.
% 3.24/1.01  sup_time_generating:                    0.
% 3.24/1.01  sup_time_sim_full:                      0.
% 3.24/1.01  sup_time_sim_immed:                     0.
% 3.24/1.01  
% 3.24/1.01  sup_num_of_clauses:                     53
% 3.24/1.01  sup_num_in_active:                      38
% 3.24/1.01  sup_num_in_passive:                     15
% 3.24/1.01  sup_num_of_loops:                       109
% 3.24/1.01  sup_fw_superposition:                   136
% 3.24/1.01  sup_bw_superposition:                   186
% 3.24/1.01  sup_immediate_simplified:               74
% 3.24/1.01  sup_given_eliminated:                   1
% 3.24/1.01  comparisons_done:                       0
% 3.24/1.01  comparisons_avoided:                    30
% 3.24/1.01  
% 3.24/1.01  ------ Simplifications
% 3.24/1.01  
% 3.24/1.01  
% 3.24/1.01  sim_fw_subset_subsumed:                 66
% 3.24/1.01  sim_bw_subset_subsumed:                 18
% 3.24/1.01  sim_fw_subsumed:                        6
% 3.24/1.01  sim_bw_subsumed:                        2
% 3.24/1.01  sim_fw_subsumption_res:                 4
% 3.24/1.01  sim_bw_subsumption_res:                 0
% 3.24/1.01  sim_tautology_del:                      0
% 3.24/1.01  sim_eq_tautology_del:                   44
% 3.24/1.01  sim_eq_res_simp:                        2
% 3.24/1.01  sim_fw_demodulated:                     2
% 3.24/1.01  sim_bw_demodulated:                     67
% 3.24/1.01  sim_light_normalised:                   8
% 3.24/1.01  sim_joinable_taut:                      0
% 3.24/1.01  sim_joinable_simp:                      0
% 3.24/1.01  sim_ac_normalised:                      0
% 3.24/1.01  sim_smt_subsumption:                    0
% 3.24/1.01  
%------------------------------------------------------------------------------
