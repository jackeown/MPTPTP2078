%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:34 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 143 expanded)
%              Number of clauses        :   35 (  36 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  228 ( 387 expanded)
%              Number of equality atoms :   95 ( 190 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f42])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f79])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f60,f80])).

fof(f109,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f92])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f93,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f67,f80])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f61,f80])).

fof(f107,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f91])).

fof(f108,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f107])).

fof(f15,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f15])).

fof(f23,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f44])).

fof(f78,plain,(
    k1_setfam_1(k1_tarski(sK4)) != sK4 ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(definition_unfolding,[],[f78,f80])).

cnf(c_28,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_tarski(X1,k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_13780,plain,
    ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
    | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
    inference(resolution,[status(thm)],[c_28,c_17])).

cnf(c_13782,plain,
    ( r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_13780])).

cnf(c_493,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_13760,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_13762,plain,
    ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | ~ r1_tarski(sK4,sK4)
    | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_13760])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,sK3(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_13636,plain,
    ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
    | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_12278,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))))) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_494,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_11431,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_11464,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
    | r2_hidden(X3,k1_xboole_0)
    | X3 != X0
    | k1_xboole_0 != k2_enumset1(X1,X1,X2,X0) ),
    inference(instantiation,[status(thm)],[c_11431])).

cnf(c_11466,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_11464])).

cnf(c_26,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11178,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))))
    | m1_subset_1(sK4,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))))
    | ~ r2_hidden(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_11206,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))))
    | ~ r2_hidden(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11178])).

cnf(c_18,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_23,plain,
    ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8239,plain,
    ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8538,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_8239])).

cnf(c_8539,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8538])).

cnf(c_8541,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_8539])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7474,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))))
    | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1902,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
    | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
    | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_86,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_65,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_62,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_29,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f97])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13782,c_13762,c_13636,c_12278,c_11466,c_11206,c_8541,c_7474,c_1902,c_86,c_65,c_62,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.73/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/1.01  
% 3.73/1.01  ------  iProver source info
% 3.73/1.01  
% 3.73/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.73/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/1.01  git: non_committed_changes: false
% 3.73/1.01  git: last_make_outside_of_git: false
% 3.73/1.01  
% 3.73/1.01  ------ 
% 3.73/1.01  ------ Parsing...
% 3.73/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  ------ Proving...
% 3.73/1.01  ------ Problem Properties 
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  clauses                                 29
% 3.73/1.01  conjectures                             1
% 3.73/1.01  EPR                                     3
% 3.73/1.01  Horn                                    22
% 3.73/1.01  unary                                   10
% 3.73/1.01  binary                                  6
% 3.73/1.01  lits                                    64
% 3.73/1.01  lits eq                                 24
% 3.73/1.01  fd_pure                                 0
% 3.73/1.01  fd_pseudo                               0
% 3.73/1.01  fd_cond                                 2
% 3.73/1.01  fd_pseudo_cond                          8
% 3.73/1.01  AC symbols                              0
% 3.73/1.01  
% 3.73/1.01  ------ Input Options Time Limit: Unbounded
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing...
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.73/1.01  Current options:
% 3.73/1.01  ------ 
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing...
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.01  
% 3.73/1.01  ------ Proving...
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  % SZS status Theorem for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  fof(f14,axiom,(
% 3.73/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f21,plain,(
% 3.73/1.01    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.73/1.01    inference(ennf_transformation,[],[f14])).
% 3.73/1.01  
% 3.73/1.01  fof(f22,plain,(
% 3.73/1.01    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 3.73/1.01    inference(flattening,[],[f21])).
% 3.73/1.01  
% 3.73/1.01  fof(f42,plain,(
% 3.73/1.01    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 3.73/1.01    introduced(choice_axiom,[])).
% 3.73/1.01  
% 3.73/1.01  fof(f43,plain,(
% 3.73/1.01    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 3.73/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f42])).
% 3.73/1.01  
% 3.73/1.01  fof(f76,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f43])).
% 3.73/1.01  
% 3.73/1.01  fof(f4,axiom,(
% 3.73/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f35,plain,(
% 3.73/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.73/1.01    inference(nnf_transformation,[],[f4])).
% 3.73/1.01  
% 3.73/1.01  fof(f36,plain,(
% 3.73/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.73/1.01    inference(rectify,[],[f35])).
% 3.73/1.01  
% 3.73/1.01  fof(f37,plain,(
% 3.73/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.73/1.01    introduced(choice_axiom,[])).
% 3.73/1.01  
% 3.73/1.01  fof(f38,plain,(
% 3.73/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.73/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 3.73/1.01  
% 3.73/1.01  fof(f60,plain,(
% 3.73/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.73/1.01    inference(cnf_transformation,[],[f38])).
% 3.73/1.01  
% 3.73/1.01  fof(f5,axiom,(
% 3.73/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f64,plain,(
% 3.73/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f5])).
% 3.73/1.01  
% 3.73/1.01  fof(f6,axiom,(
% 3.73/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f65,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f6])).
% 3.73/1.01  
% 3.73/1.01  fof(f7,axiom,(
% 3.73/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f66,plain,(
% 3.73/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f7])).
% 3.73/1.01  
% 3.73/1.01  fof(f79,plain,(
% 3.73/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.73/1.01    inference(definition_unfolding,[],[f65,f66])).
% 3.73/1.01  
% 3.73/1.01  fof(f80,plain,(
% 3.73/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.73/1.01    inference(definition_unfolding,[],[f64,f79])).
% 3.73/1.01  
% 3.73/1.01  fof(f92,plain,(
% 3.73/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.73/1.01    inference(definition_unfolding,[],[f60,f80])).
% 3.73/1.01  
% 3.73/1.01  fof(f109,plain,(
% 3.73/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.73/1.01    inference(equality_resolution,[],[f92])).
% 3.73/1.01  
% 3.73/1.01  fof(f77,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK3(X0,X1))) )),
% 3.73/1.01    inference(cnf_transformation,[],[f43])).
% 3.73/1.01  
% 3.73/1.01  fof(f10,axiom,(
% 3.73/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f71,plain,(
% 3.73/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.73/1.01    inference(cnf_transformation,[],[f10])).
% 3.73/1.01  
% 3.73/1.01  fof(f13,axiom,(
% 3.73/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f19,plain,(
% 3.73/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.73/1.01    inference(ennf_transformation,[],[f13])).
% 3.73/1.01  
% 3.73/1.01  fof(f20,plain,(
% 3.73/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.73/1.01    inference(flattening,[],[f19])).
% 3.73/1.01  
% 3.73/1.01  fof(f75,plain,(
% 3.73/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f20])).
% 3.73/1.01  
% 3.73/1.01  fof(f8,axiom,(
% 3.73/1.01    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f67,plain,(
% 3.73/1.01    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 3.73/1.01    inference(cnf_transformation,[],[f8])).
% 3.73/1.01  
% 3.73/1.01  fof(f93,plain,(
% 3.73/1.01    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 3.73/1.01    inference(definition_unfolding,[],[f67,f80])).
% 3.73/1.01  
% 3.73/1.01  fof(f11,axiom,(
% 3.73/1.01    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f72,plain,(
% 3.73/1.01    ( ! [X0] : (r1_tarski(k1_setfam_1(X0),k3_tarski(X0))) )),
% 3.73/1.01    inference(cnf_transformation,[],[f11])).
% 3.73/1.01  
% 3.73/1.01  fof(f12,axiom,(
% 3.73/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f41,plain,(
% 3.73/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.73/1.01    inference(nnf_transformation,[],[f12])).
% 3.73/1.01  
% 3.73/1.01  fof(f73,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.73/1.01    inference(cnf_transformation,[],[f41])).
% 3.73/1.01  
% 3.73/1.01  fof(f2,axiom,(
% 3.73/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f28,plain,(
% 3.73/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.01    inference(nnf_transformation,[],[f2])).
% 3.73/1.01  
% 3.73/1.01  fof(f29,plain,(
% 3.73/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.01    inference(flattening,[],[f28])).
% 3.73/1.01  
% 3.73/1.01  fof(f51,plain,(
% 3.73/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.73/1.01    inference(cnf_transformation,[],[f29])).
% 3.73/1.01  
% 3.73/1.01  fof(f49,plain,(
% 3.73/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.73/1.01    inference(cnf_transformation,[],[f29])).
% 3.73/1.01  
% 3.73/1.01  fof(f99,plain,(
% 3.73/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.73/1.01    inference(equality_resolution,[],[f49])).
% 3.73/1.01  
% 3.73/1.01  fof(f61,plain,(
% 3.73/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.73/1.01    inference(cnf_transformation,[],[f38])).
% 3.73/1.01  
% 3.73/1.01  fof(f91,plain,(
% 3.73/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.73/1.01    inference(definition_unfolding,[],[f61,f80])).
% 3.73/1.01  
% 3.73/1.01  fof(f107,plain,(
% 3.73/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 3.73/1.01    inference(equality_resolution,[],[f91])).
% 3.73/1.01  
% 3.73/1.01  fof(f108,plain,(
% 3.73/1.01    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 3.73/1.01    inference(equality_resolution,[],[f107])).
% 3.73/1.01  
% 3.73/1.01  fof(f15,conjecture,(
% 3.73/1.01    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.73/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.01  
% 3.73/1.01  fof(f16,negated_conjecture,(
% 3.73/1.01    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.73/1.01    inference(negated_conjecture,[],[f15])).
% 3.73/1.01  
% 3.73/1.01  fof(f23,plain,(
% 3.73/1.01    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 3.73/1.01    inference(ennf_transformation,[],[f16])).
% 3.73/1.01  
% 3.73/1.01  fof(f44,plain,(
% 3.73/1.01    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.73/1.01    introduced(choice_axiom,[])).
% 3.73/1.01  
% 3.73/1.01  fof(f45,plain,(
% 3.73/1.01    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.73/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f44])).
% 3.73/1.01  
% 3.73/1.01  fof(f78,plain,(
% 3.73/1.01    k1_setfam_1(k1_tarski(sK4)) != sK4),
% 3.73/1.01    inference(cnf_transformation,[],[f45])).
% 3.73/1.01  
% 3.73/1.01  fof(f97,plain,(
% 3.73/1.01    k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4),
% 3.73/1.01    inference(definition_unfolding,[],[f78,f80])).
% 3.73/1.01  
% 3.73/1.01  cnf(c_28,plain,
% 3.73/1.01      ( r2_hidden(sK3(X0,X1),X0)
% 3.73/1.01      | r1_tarski(X1,k1_setfam_1(X0))
% 3.73/1.01      | k1_xboole_0 = X0 ),
% 3.73/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_17,plain,
% 3.73/1.01      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.73/1.01      inference(cnf_transformation,[],[f109]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_13780,plain,
% 3.73/1.01      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
% 3.73/1.01      | sK3(k2_enumset1(X1,X1,X1,X1),X0) = X1
% 3.73/1.01      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ),
% 3.73/1.01      inference(resolution,[status(thm)],[c_28,c_17]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_13782,plain,
% 3.73/1.01      ( r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.73/1.01      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) = sK4
% 3.73/1.01      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_13780]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_493,plain,
% 3.73/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.73/1.01      theory(equality) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_13760,plain,
% 3.73/1.01      ( ~ r1_tarski(X0,X1)
% 3.73/1.01      | r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 3.73/1.01      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != X1
% 3.73/1.01      | sK4 != X0 ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_493]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_13762,plain,
% 3.73/1.01      ( r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 3.73/1.01      | ~ r1_tarski(sK4,sK4)
% 3.73/1.01      | sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4) != sK4
% 3.73/1.01      | sK4 != sK4 ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_13760]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_27,plain,
% 3.73/1.01      ( ~ r1_tarski(X0,sK3(X1,X0))
% 3.73/1.01      | r1_tarski(X0,k1_setfam_1(X1))
% 3.73/1.01      | k1_xboole_0 = X1 ),
% 3.73/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_13636,plain,
% 3.73/1.01      ( ~ r1_tarski(sK4,sK3(k2_enumset1(sK4,sK4,sK4,sK4),sK4))
% 3.73/1.01      | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.73/1.01      | k1_xboole_0 = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_27]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_22,plain,
% 3.73/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.73/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_12278,plain,
% 3.73/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))))) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_22]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_494,plain,
% 3.73/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.73/1.01      theory(equality) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11431,plain,
% 3.73/1.01      ( r2_hidden(X0,X1)
% 3.73/1.01      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X4,X2))
% 3.73/1.01      | X0 != X2
% 3.73/1.01      | X1 != k2_enumset1(X3,X3,X4,X2) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_494]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11464,plain,
% 3.73/1.01      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))
% 3.73/1.01      | r2_hidden(X3,k1_xboole_0)
% 3.73/1.01      | X3 != X0
% 3.73/1.01      | k1_xboole_0 != k2_enumset1(X1,X1,X2,X0) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_11431]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11466,plain,
% 3.73/1.01      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 3.73/1.01      | r2_hidden(sK4,k1_xboole_0)
% 3.73/1.01      | sK4 != sK4
% 3.73/1.01      | k1_xboole_0 != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_11464]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_26,plain,
% 3.73/1.01      ( m1_subset_1(X0,X1)
% 3.73/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.73/1.01      | ~ r2_hidden(X0,X2) ),
% 3.73/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11178,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))))
% 3.73/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))))
% 3.73/1.01      | ~ r2_hidden(sK4,X0) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_26]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_11206,plain,
% 3.73/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))))
% 3.73/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))))
% 3.73/1.01      | ~ r2_hidden(sK4,k1_xboole_0) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_11178]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_18,plain,
% 3.73/1.01      ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 3.73/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_23,plain,
% 3.73/1.01      ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
% 3.73/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_8239,plain,
% 3.73/1.01      ( r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) = iProver_top ),
% 3.73/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_8538,plain,
% 3.73/1.01      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) = iProver_top ),
% 3.73/1.01      inference(superposition,[status(thm)],[c_18,c_8239]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_8539,plain,
% 3.73/1.01      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
% 3.73/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_8538]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_8541,plain,
% 3.73/1.01      ( r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_8539]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_25,plain,
% 3.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.73/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_7474,plain,
% 3.73/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))))
% 3.73/1.01      | r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_25]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_3,plain,
% 3.73/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.73/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_1902,plain,
% 3.73/1.01      ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)),sK4)
% 3.73/1.01      | ~ r1_tarski(sK4,k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)))
% 3.73/1.01      | k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_5,plain,
% 3.73/1.01      ( r1_tarski(X0,X0) ),
% 3.73/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_86,plain,
% 3.73/1.01      ( r1_tarski(sK4,sK4) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_16,plain,
% 3.73/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 3.73/1.01      inference(cnf_transformation,[],[f108]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_65,plain,
% 3.73/1.01      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_62,plain,
% 3.73/1.01      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 3.73/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(c_29,negated_conjecture,
% 3.73/1.01      ( k1_setfam_1(k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
% 3.73/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.73/1.01  
% 3.73/1.01  cnf(contradiction,plain,
% 3.73/1.01      ( $false ),
% 3.73/1.01      inference(minisat,
% 3.73/1.01                [status(thm)],
% 3.73/1.01                [c_13782,c_13762,c_13636,c_12278,c_11466,c_11206,c_8541,
% 3.73/1.01                 c_7474,c_1902,c_86,c_65,c_62,c_29]) ).
% 3.73/1.01  
% 3.73/1.01  
% 3.73/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/1.01  
% 3.73/1.01  ------                               Statistics
% 3.73/1.01  
% 3.73/1.01  ------ Selected
% 3.73/1.01  
% 3.73/1.01  total_time:                             0.387
% 3.73/1.01  
%------------------------------------------------------------------------------
