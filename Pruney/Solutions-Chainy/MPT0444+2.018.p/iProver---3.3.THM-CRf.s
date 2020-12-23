%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:02 EST 2020

% Result     : Theorem 15.23s
% Output     : CNFRefutation 15.23s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 932 expanded)
%              Number of clauses        :   72 ( 370 expanded)
%              Number of leaves         :   19 ( 214 expanded)
%              Depth                    :   19
%              Number of atoms          :  229 (1645 expanded)
%              Number of equality atoms :   89 ( 655 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f42,f60,f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f39,f60,f40,f40,f60])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f41,f40,f40])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f32,f31])).

fof(f58,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ~ r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f58,f40,f40])).

fof(f56,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_8,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_765,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_770,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1514,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_765,c_770])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_763,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1526,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1514,c_763])).

cnf(c_7,plain,
    ( k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1602,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1526,c_7])).

cnf(c_5,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_766,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7037,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1602,c_766])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1605,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1526,c_6])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_767,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2053,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_767])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_769,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2360,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2053,c_769])).

cnf(c_2384,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_770])).

cnf(c_2637,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
    inference(superposition,[status(thm)],[c_2384,c_763])).

cnf(c_1588,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_1526])).

cnf(c_2797,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_2637,c_1588])).

cnf(c_7039,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X0))),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7037,c_2797])).

cnf(c_2762,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))),X3)) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_2637])).

cnf(c_2803,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),X3)))) = X0 ),
    inference(demodulation,[status(thm)],[c_2762,c_6])).

cnf(c_2052,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1605,c_6])).

cnf(c_5607,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),X3))) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2803,c_2052])).

cnf(c_2381,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_2360])).

cnf(c_2525,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2381,c_763])).

cnf(c_4464,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2525,c_1605])).

cnf(c_4462,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X3) ),
    inference(superposition,[status(thm)],[c_2525,c_6])).

cnf(c_4521,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),X3) ),
    inference(demodulation,[status(thm)],[c_4462,c_4464])).

cnf(c_2524,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2381,c_770])).

cnf(c_2660,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2524,c_763])).

cnf(c_4595,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),X3)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2660,c_2637])).

cnf(c_5777,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_5607,c_4464,c_4521,c_4595])).

cnf(c_6053,plain,
    ( k3_tarski(k2_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5777,c_7])).

cnf(c_6138,plain,
    ( k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_6053,c_2525])).

cnf(c_7040,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7039,c_6138])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_109,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_15,c_13])).

cnf(c_110,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_109])).

cnf(c_757,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_110])).

cnf(c_2237,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_769])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_762,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_761,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5008,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0)) != iProver_top
    | r1_xboole_0(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_762,c_761])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_23,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_791,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))))
    | ~ r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0))
    | ~ r1_xboole_0(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_792,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) = iProver_top
    | r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0)) != iProver_top
    | r1_xboole_0(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_809,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_810,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) != iProver_top
    | r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_847,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_848,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_6007,plain,
    ( r1_xboole_0(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5008,c_21,c_23,c_792,c_810,c_848])).

cnf(c_51624,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_6007])).

cnf(c_51898,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_757,c_51624])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18976,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_18977,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) != iProver_top
    | r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18976])).

cnf(c_56136,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51898,c_22,c_18977,c_51624])).

cnf(c_56140,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_7040,c_56136])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:46:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.23/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.23/2.49  
% 15.23/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.23/2.49  
% 15.23/2.49  ------  iProver source info
% 15.23/2.49  
% 15.23/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.23/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.23/2.49  git: non_committed_changes: false
% 15.23/2.49  git: last_make_outside_of_git: false
% 15.23/2.49  
% 15.23/2.49  ------ 
% 15.23/2.49  
% 15.23/2.49  ------ Input Options
% 15.23/2.49  
% 15.23/2.49  --out_options                           all
% 15.23/2.49  --tptp_safe_out                         true
% 15.23/2.49  --problem_path                          ""
% 15.23/2.49  --include_path                          ""
% 15.23/2.49  --clausifier                            res/vclausify_rel
% 15.23/2.49  --clausifier_options                    ""
% 15.23/2.49  --stdin                                 false
% 15.23/2.49  --stats_out                             all
% 15.23/2.49  
% 15.23/2.49  ------ General Options
% 15.23/2.49  
% 15.23/2.49  --fof                                   false
% 15.23/2.49  --time_out_real                         305.
% 15.23/2.49  --time_out_virtual                      -1.
% 15.23/2.49  --symbol_type_check                     false
% 15.23/2.49  --clausify_out                          false
% 15.23/2.49  --sig_cnt_out                           false
% 15.23/2.49  --trig_cnt_out                          false
% 15.23/2.49  --trig_cnt_out_tolerance                1.
% 15.23/2.49  --trig_cnt_out_sk_spl                   false
% 15.23/2.49  --abstr_cl_out                          false
% 15.23/2.49  
% 15.23/2.49  ------ Global Options
% 15.23/2.49  
% 15.23/2.49  --schedule                              default
% 15.23/2.49  --add_important_lit                     false
% 15.23/2.49  --prop_solver_per_cl                    1000
% 15.23/2.49  --min_unsat_core                        false
% 15.23/2.49  --soft_assumptions                      false
% 15.23/2.49  --soft_lemma_size                       3
% 15.23/2.49  --prop_impl_unit_size                   0
% 15.23/2.49  --prop_impl_unit                        []
% 15.23/2.49  --share_sel_clauses                     true
% 15.23/2.49  --reset_solvers                         false
% 15.23/2.49  --bc_imp_inh                            [conj_cone]
% 15.23/2.49  --conj_cone_tolerance                   3.
% 15.23/2.49  --extra_neg_conj                        none
% 15.23/2.49  --large_theory_mode                     true
% 15.23/2.49  --prolific_symb_bound                   200
% 15.23/2.49  --lt_threshold                          2000
% 15.23/2.49  --clause_weak_htbl                      true
% 15.23/2.49  --gc_record_bc_elim                     false
% 15.23/2.49  
% 15.23/2.49  ------ Preprocessing Options
% 15.23/2.49  
% 15.23/2.49  --preprocessing_flag                    true
% 15.23/2.49  --time_out_prep_mult                    0.1
% 15.23/2.49  --splitting_mode                        input
% 15.23/2.49  --splitting_grd                         true
% 15.23/2.49  --splitting_cvd                         false
% 15.23/2.49  --splitting_cvd_svl                     false
% 15.23/2.49  --splitting_nvd                         32
% 15.23/2.49  --sub_typing                            true
% 15.23/2.49  --prep_gs_sim                           true
% 15.23/2.49  --prep_unflatten                        true
% 15.23/2.49  --prep_res_sim                          true
% 15.23/2.49  --prep_upred                            true
% 15.23/2.49  --prep_sem_filter                       exhaustive
% 15.23/2.49  --prep_sem_filter_out                   false
% 15.23/2.49  --pred_elim                             true
% 15.23/2.49  --res_sim_input                         true
% 15.23/2.49  --eq_ax_congr_red                       true
% 15.23/2.49  --pure_diseq_elim                       true
% 15.23/2.49  --brand_transform                       false
% 15.23/2.49  --non_eq_to_eq                          false
% 15.23/2.49  --prep_def_merge                        true
% 15.23/2.49  --prep_def_merge_prop_impl              false
% 15.23/2.49  --prep_def_merge_mbd                    true
% 15.23/2.49  --prep_def_merge_tr_red                 false
% 15.23/2.49  --prep_def_merge_tr_cl                  false
% 15.23/2.49  --smt_preprocessing                     true
% 15.23/2.49  --smt_ac_axioms                         fast
% 15.23/2.49  --preprocessed_out                      false
% 15.23/2.49  --preprocessed_stats                    false
% 15.23/2.49  
% 15.23/2.49  ------ Abstraction refinement Options
% 15.23/2.49  
% 15.23/2.49  --abstr_ref                             []
% 15.23/2.49  --abstr_ref_prep                        false
% 15.23/2.49  --abstr_ref_until_sat                   false
% 15.23/2.49  --abstr_ref_sig_restrict                funpre
% 15.23/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.23/2.49  --abstr_ref_under                       []
% 15.23/2.49  
% 15.23/2.49  ------ SAT Options
% 15.23/2.49  
% 15.23/2.49  --sat_mode                              false
% 15.23/2.49  --sat_fm_restart_options                ""
% 15.23/2.49  --sat_gr_def                            false
% 15.23/2.49  --sat_epr_types                         true
% 15.23/2.49  --sat_non_cyclic_types                  false
% 15.23/2.49  --sat_finite_models                     false
% 15.23/2.49  --sat_fm_lemmas                         false
% 15.23/2.49  --sat_fm_prep                           false
% 15.23/2.49  --sat_fm_uc_incr                        true
% 15.23/2.49  --sat_out_model                         small
% 15.23/2.49  --sat_out_clauses                       false
% 15.23/2.49  
% 15.23/2.49  ------ QBF Options
% 15.23/2.49  
% 15.23/2.49  --qbf_mode                              false
% 15.23/2.49  --qbf_elim_univ                         false
% 15.23/2.49  --qbf_dom_inst                          none
% 15.23/2.49  --qbf_dom_pre_inst                      false
% 15.23/2.49  --qbf_sk_in                             false
% 15.23/2.49  --qbf_pred_elim                         true
% 15.23/2.49  --qbf_split                             512
% 15.23/2.49  
% 15.23/2.49  ------ BMC1 Options
% 15.23/2.49  
% 15.23/2.49  --bmc1_incremental                      false
% 15.23/2.49  --bmc1_axioms                           reachable_all
% 15.23/2.49  --bmc1_min_bound                        0
% 15.23/2.49  --bmc1_max_bound                        -1
% 15.23/2.49  --bmc1_max_bound_default                -1
% 15.23/2.49  --bmc1_symbol_reachability              true
% 15.23/2.49  --bmc1_property_lemmas                  false
% 15.23/2.49  --bmc1_k_induction                      false
% 15.23/2.49  --bmc1_non_equiv_states                 false
% 15.23/2.49  --bmc1_deadlock                         false
% 15.23/2.49  --bmc1_ucm                              false
% 15.23/2.49  --bmc1_add_unsat_core                   none
% 15.23/2.49  --bmc1_unsat_core_children              false
% 15.23/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.23/2.49  --bmc1_out_stat                         full
% 15.23/2.49  --bmc1_ground_init                      false
% 15.23/2.49  --bmc1_pre_inst_next_state              false
% 15.23/2.49  --bmc1_pre_inst_state                   false
% 15.23/2.49  --bmc1_pre_inst_reach_state             false
% 15.23/2.49  --bmc1_out_unsat_core                   false
% 15.23/2.49  --bmc1_aig_witness_out                  false
% 15.23/2.49  --bmc1_verbose                          false
% 15.23/2.49  --bmc1_dump_clauses_tptp                false
% 15.23/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.23/2.49  --bmc1_dump_file                        -
% 15.23/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.23/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.23/2.49  --bmc1_ucm_extend_mode                  1
% 15.23/2.49  --bmc1_ucm_init_mode                    2
% 15.23/2.49  --bmc1_ucm_cone_mode                    none
% 15.23/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.23/2.49  --bmc1_ucm_relax_model                  4
% 15.23/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.23/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.23/2.49  --bmc1_ucm_layered_model                none
% 15.23/2.49  --bmc1_ucm_max_lemma_size               10
% 15.23/2.49  
% 15.23/2.49  ------ AIG Options
% 15.23/2.49  
% 15.23/2.49  --aig_mode                              false
% 15.23/2.49  
% 15.23/2.49  ------ Instantiation Options
% 15.23/2.49  
% 15.23/2.49  --instantiation_flag                    true
% 15.23/2.49  --inst_sos_flag                         true
% 15.23/2.49  --inst_sos_phase                        true
% 15.23/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.23/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.23/2.49  --inst_lit_sel_side                     num_symb
% 15.23/2.49  --inst_solver_per_active                1400
% 15.23/2.49  --inst_solver_calls_frac                1.
% 15.23/2.49  --inst_passive_queue_type               priority_queues
% 15.23/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.23/2.49  --inst_passive_queues_freq              [25;2]
% 15.23/2.49  --inst_dismatching                      true
% 15.23/2.49  --inst_eager_unprocessed_to_passive     true
% 15.23/2.49  --inst_prop_sim_given                   true
% 15.23/2.49  --inst_prop_sim_new                     false
% 15.23/2.49  --inst_subs_new                         false
% 15.23/2.49  --inst_eq_res_simp                      false
% 15.23/2.49  --inst_subs_given                       false
% 15.23/2.49  --inst_orphan_elimination               true
% 15.23/2.49  --inst_learning_loop_flag               true
% 15.23/2.49  --inst_learning_start                   3000
% 15.23/2.49  --inst_learning_factor                  2
% 15.23/2.49  --inst_start_prop_sim_after_learn       3
% 15.23/2.49  --inst_sel_renew                        solver
% 15.23/2.49  --inst_lit_activity_flag                true
% 15.23/2.49  --inst_restr_to_given                   false
% 15.23/2.49  --inst_activity_threshold               500
% 15.23/2.49  --inst_out_proof                        true
% 15.23/2.49  
% 15.23/2.49  ------ Resolution Options
% 15.23/2.49  
% 15.23/2.49  --resolution_flag                       true
% 15.23/2.49  --res_lit_sel                           adaptive
% 15.23/2.49  --res_lit_sel_side                      none
% 15.23/2.49  --res_ordering                          kbo
% 15.23/2.49  --res_to_prop_solver                    active
% 15.23/2.49  --res_prop_simpl_new                    false
% 15.23/2.49  --res_prop_simpl_given                  true
% 15.23/2.49  --res_passive_queue_type                priority_queues
% 15.23/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.23/2.49  --res_passive_queues_freq               [15;5]
% 15.23/2.49  --res_forward_subs                      full
% 15.23/2.49  --res_backward_subs                     full
% 15.23/2.49  --res_forward_subs_resolution           true
% 15.23/2.49  --res_backward_subs_resolution          true
% 15.23/2.49  --res_orphan_elimination                true
% 15.23/2.49  --res_time_limit                        2.
% 15.23/2.49  --res_out_proof                         true
% 15.23/2.49  
% 15.23/2.49  ------ Superposition Options
% 15.23/2.49  
% 15.23/2.49  --superposition_flag                    true
% 15.23/2.49  --sup_passive_queue_type                priority_queues
% 15.23/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.23/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.23/2.49  --demod_completeness_check              fast
% 15.23/2.49  --demod_use_ground                      true
% 15.23/2.49  --sup_to_prop_solver                    passive
% 15.23/2.49  --sup_prop_simpl_new                    true
% 15.23/2.49  --sup_prop_simpl_given                  true
% 15.23/2.49  --sup_fun_splitting                     true
% 15.23/2.49  --sup_smt_interval                      50000
% 15.23/2.49  
% 15.23/2.49  ------ Superposition Simplification Setup
% 15.23/2.49  
% 15.23/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.23/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.23/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.23/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.23/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.23/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.23/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.23/2.49  --sup_immed_triv                        [TrivRules]
% 15.23/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.23/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.23/2.49  --sup_immed_bw_main                     []
% 15.23/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.23/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.23/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.23/2.49  --sup_input_bw                          []
% 15.23/2.49  
% 15.23/2.49  ------ Combination Options
% 15.23/2.49  
% 15.23/2.49  --comb_res_mult                         3
% 15.23/2.49  --comb_sup_mult                         2
% 15.23/2.49  --comb_inst_mult                        10
% 15.23/2.49  
% 15.23/2.49  ------ Debug Options
% 15.23/2.49  
% 15.23/2.49  --dbg_backtrace                         false
% 15.23/2.49  --dbg_dump_prop_clauses                 false
% 15.23/2.49  --dbg_dump_prop_clauses_file            -
% 15.23/2.49  --dbg_out_stat                          false
% 15.23/2.49  ------ Parsing...
% 15.23/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.23/2.49  
% 15.23/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.23/2.49  
% 15.23/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.23/2.49  
% 15.23/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.23/2.49  ------ Proving...
% 15.23/2.49  ------ Problem Properties 
% 15.23/2.49  
% 15.23/2.49  
% 15.23/2.49  clauses                                 19
% 15.23/2.49  conjectures                             3
% 15.23/2.49  EPR                                     4
% 15.23/2.49  Horn                                    19
% 15.23/2.49  unary                                   10
% 15.23/2.49  binary                                  5
% 15.23/2.49  lits                                    32
% 15.23/2.49  lits eq                                 6
% 15.23/2.49  fd_pure                                 0
% 15.23/2.49  fd_pseudo                               0
% 15.23/2.49  fd_cond                                 0
% 15.23/2.49  fd_pseudo_cond                          0
% 15.23/2.49  AC symbols                              0
% 15.23/2.49  
% 15.23/2.49  ------ Schedule dynamic 5 is on 
% 15.23/2.49  
% 15.23/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.23/2.49  
% 15.23/2.49  
% 15.23/2.49  ------ 
% 15.23/2.49  Current options:
% 15.23/2.49  ------ 
% 15.23/2.49  
% 15.23/2.49  ------ Input Options
% 15.23/2.49  
% 15.23/2.49  --out_options                           all
% 15.23/2.49  --tptp_safe_out                         true
% 15.23/2.49  --problem_path                          ""
% 15.23/2.49  --include_path                          ""
% 15.23/2.49  --clausifier                            res/vclausify_rel
% 15.23/2.49  --clausifier_options                    ""
% 15.23/2.49  --stdin                                 false
% 15.23/2.49  --stats_out                             all
% 15.23/2.49  
% 15.23/2.49  ------ General Options
% 15.23/2.49  
% 15.23/2.49  --fof                                   false
% 15.23/2.49  --time_out_real                         305.
% 15.23/2.49  --time_out_virtual                      -1.
% 15.23/2.49  --symbol_type_check                     false
% 15.23/2.49  --clausify_out                          false
% 15.23/2.49  --sig_cnt_out                           false
% 15.23/2.49  --trig_cnt_out                          false
% 15.23/2.49  --trig_cnt_out_tolerance                1.
% 15.23/2.49  --trig_cnt_out_sk_spl                   false
% 15.23/2.49  --abstr_cl_out                          false
% 15.23/2.49  
% 15.23/2.49  ------ Global Options
% 15.23/2.49  
% 15.23/2.49  --schedule                              default
% 15.23/2.49  --add_important_lit                     false
% 15.23/2.49  --prop_solver_per_cl                    1000
% 15.23/2.49  --min_unsat_core                        false
% 15.23/2.49  --soft_assumptions                      false
% 15.23/2.49  --soft_lemma_size                       3
% 15.23/2.49  --prop_impl_unit_size                   0
% 15.23/2.49  --prop_impl_unit                        []
% 15.23/2.49  --share_sel_clauses                     true
% 15.23/2.49  --reset_solvers                         false
% 15.23/2.49  --bc_imp_inh                            [conj_cone]
% 15.23/2.49  --conj_cone_tolerance                   3.
% 15.23/2.49  --extra_neg_conj                        none
% 15.23/2.49  --large_theory_mode                     true
% 15.23/2.49  --prolific_symb_bound                   200
% 15.23/2.49  --lt_threshold                          2000
% 15.23/2.49  --clause_weak_htbl                      true
% 15.23/2.49  --gc_record_bc_elim                     false
% 15.23/2.49  
% 15.23/2.49  ------ Preprocessing Options
% 15.23/2.49  
% 15.23/2.49  --preprocessing_flag                    true
% 15.23/2.49  --time_out_prep_mult                    0.1
% 15.23/2.49  --splitting_mode                        input
% 15.23/2.49  --splitting_grd                         true
% 15.23/2.49  --splitting_cvd                         false
% 15.23/2.49  --splitting_cvd_svl                     false
% 15.23/2.49  --splitting_nvd                         32
% 15.23/2.49  --sub_typing                            true
% 15.23/2.49  --prep_gs_sim                           true
% 15.23/2.49  --prep_unflatten                        true
% 15.23/2.49  --prep_res_sim                          true
% 15.23/2.49  --prep_upred                            true
% 15.23/2.49  --prep_sem_filter                       exhaustive
% 15.23/2.49  --prep_sem_filter_out                   false
% 15.23/2.49  --pred_elim                             true
% 15.23/2.49  --res_sim_input                         true
% 15.23/2.49  --eq_ax_congr_red                       true
% 15.23/2.49  --pure_diseq_elim                       true
% 15.23/2.49  --brand_transform                       false
% 15.23/2.49  --non_eq_to_eq                          false
% 15.23/2.49  --prep_def_merge                        true
% 15.23/2.49  --prep_def_merge_prop_impl              false
% 15.23/2.49  --prep_def_merge_mbd                    true
% 15.23/2.49  --prep_def_merge_tr_red                 false
% 15.23/2.49  --prep_def_merge_tr_cl                  false
% 15.23/2.49  --smt_preprocessing                     true
% 15.23/2.49  --smt_ac_axioms                         fast
% 15.23/2.49  --preprocessed_out                      false
% 15.23/2.49  --preprocessed_stats                    false
% 15.23/2.49  
% 15.23/2.49  ------ Abstraction refinement Options
% 15.23/2.49  
% 15.23/2.49  --abstr_ref                             []
% 15.23/2.49  --abstr_ref_prep                        false
% 15.23/2.49  --abstr_ref_until_sat                   false
% 15.23/2.49  --abstr_ref_sig_restrict                funpre
% 15.23/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.23/2.49  --abstr_ref_under                       []
% 15.23/2.49  
% 15.23/2.49  ------ SAT Options
% 15.23/2.49  
% 15.23/2.49  --sat_mode                              false
% 15.23/2.49  --sat_fm_restart_options                ""
% 15.23/2.49  --sat_gr_def                            false
% 15.23/2.49  --sat_epr_types                         true
% 15.23/2.49  --sat_non_cyclic_types                  false
% 15.23/2.49  --sat_finite_models                     false
% 15.23/2.49  --sat_fm_lemmas                         false
% 15.23/2.49  --sat_fm_prep                           false
% 15.23/2.49  --sat_fm_uc_incr                        true
% 15.23/2.49  --sat_out_model                         small
% 15.23/2.49  --sat_out_clauses                       false
% 15.23/2.49  
% 15.23/2.49  ------ QBF Options
% 15.23/2.49  
% 15.23/2.49  --qbf_mode                              false
% 15.23/2.49  --qbf_elim_univ                         false
% 15.23/2.49  --qbf_dom_inst                          none
% 15.23/2.49  --qbf_dom_pre_inst                      false
% 15.23/2.49  --qbf_sk_in                             false
% 15.23/2.49  --qbf_pred_elim                         true
% 15.23/2.49  --qbf_split                             512
% 15.23/2.49  
% 15.23/2.49  ------ BMC1 Options
% 15.23/2.49  
% 15.23/2.49  --bmc1_incremental                      false
% 15.23/2.49  --bmc1_axioms                           reachable_all
% 15.23/2.49  --bmc1_min_bound                        0
% 15.23/2.49  --bmc1_max_bound                        -1
% 15.23/2.49  --bmc1_max_bound_default                -1
% 15.23/2.49  --bmc1_symbol_reachability              true
% 15.23/2.49  --bmc1_property_lemmas                  false
% 15.23/2.49  --bmc1_k_induction                      false
% 15.23/2.49  --bmc1_non_equiv_states                 false
% 15.23/2.49  --bmc1_deadlock                         false
% 15.23/2.49  --bmc1_ucm                              false
% 15.23/2.49  --bmc1_add_unsat_core                   none
% 15.23/2.49  --bmc1_unsat_core_children              false
% 15.23/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.23/2.49  --bmc1_out_stat                         full
% 15.23/2.49  --bmc1_ground_init                      false
% 15.23/2.49  --bmc1_pre_inst_next_state              false
% 15.23/2.49  --bmc1_pre_inst_state                   false
% 15.23/2.49  --bmc1_pre_inst_reach_state             false
% 15.23/2.49  --bmc1_out_unsat_core                   false
% 15.23/2.49  --bmc1_aig_witness_out                  false
% 15.23/2.49  --bmc1_verbose                          false
% 15.23/2.49  --bmc1_dump_clauses_tptp                false
% 15.23/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.23/2.49  --bmc1_dump_file                        -
% 15.23/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.23/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.23/2.49  --bmc1_ucm_extend_mode                  1
% 15.23/2.49  --bmc1_ucm_init_mode                    2
% 15.23/2.49  --bmc1_ucm_cone_mode                    none
% 15.23/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.23/2.49  --bmc1_ucm_relax_model                  4
% 15.23/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.23/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.23/2.49  --bmc1_ucm_layered_model                none
% 15.23/2.49  --bmc1_ucm_max_lemma_size               10
% 15.23/2.49  
% 15.23/2.49  ------ AIG Options
% 15.23/2.49  
% 15.23/2.49  --aig_mode                              false
% 15.23/2.49  
% 15.23/2.49  ------ Instantiation Options
% 15.23/2.49  
% 15.23/2.49  --instantiation_flag                    true
% 15.23/2.49  --inst_sos_flag                         true
% 15.23/2.49  --inst_sos_phase                        true
% 15.23/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.23/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.23/2.49  --inst_lit_sel_side                     none
% 15.23/2.49  --inst_solver_per_active                1400
% 15.23/2.49  --inst_solver_calls_frac                1.
% 15.23/2.49  --inst_passive_queue_type               priority_queues
% 15.23/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.23/2.49  --inst_passive_queues_freq              [25;2]
% 15.23/2.49  --inst_dismatching                      true
% 15.23/2.49  --inst_eager_unprocessed_to_passive     true
% 15.23/2.49  --inst_prop_sim_given                   true
% 15.23/2.49  --inst_prop_sim_new                     false
% 15.23/2.49  --inst_subs_new                         false
% 15.23/2.49  --inst_eq_res_simp                      false
% 15.23/2.49  --inst_subs_given                       false
% 15.23/2.49  --inst_orphan_elimination               true
% 15.23/2.49  --inst_learning_loop_flag               true
% 15.23/2.49  --inst_learning_start                   3000
% 15.23/2.49  --inst_learning_factor                  2
% 15.23/2.49  --inst_start_prop_sim_after_learn       3
% 15.23/2.49  --inst_sel_renew                        solver
% 15.23/2.49  --inst_lit_activity_flag                true
% 15.23/2.49  --inst_restr_to_given                   false
% 15.23/2.49  --inst_activity_threshold               500
% 15.23/2.49  --inst_out_proof                        true
% 15.23/2.49  
% 15.23/2.49  ------ Resolution Options
% 15.23/2.49  
% 15.23/2.49  --resolution_flag                       false
% 15.23/2.49  --res_lit_sel                           adaptive
% 15.23/2.49  --res_lit_sel_side                      none
% 15.23/2.49  --res_ordering                          kbo
% 15.23/2.49  --res_to_prop_solver                    active
% 15.23/2.49  --res_prop_simpl_new                    false
% 15.23/2.49  --res_prop_simpl_given                  true
% 15.23/2.49  --res_passive_queue_type                priority_queues
% 15.23/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.23/2.49  --res_passive_queues_freq               [15;5]
% 15.23/2.49  --res_forward_subs                      full
% 15.23/2.49  --res_backward_subs                     full
% 15.23/2.49  --res_forward_subs_resolution           true
% 15.23/2.49  --res_backward_subs_resolution          true
% 15.23/2.49  --res_orphan_elimination                true
% 15.23/2.49  --res_time_limit                        2.
% 15.23/2.49  --res_out_proof                         true
% 15.23/2.49  
% 15.23/2.49  ------ Superposition Options
% 15.23/2.49  
% 15.23/2.49  --superposition_flag                    true
% 15.23/2.49  --sup_passive_queue_type                priority_queues
% 15.23/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.23/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.23/2.49  --demod_completeness_check              fast
% 15.23/2.49  --demod_use_ground                      true
% 15.23/2.49  --sup_to_prop_solver                    passive
% 15.23/2.49  --sup_prop_simpl_new                    true
% 15.23/2.49  --sup_prop_simpl_given                  true
% 15.23/2.49  --sup_fun_splitting                     true
% 15.23/2.49  --sup_smt_interval                      50000
% 15.23/2.49  
% 15.23/2.49  ------ Superposition Simplification Setup
% 15.23/2.49  
% 15.23/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.23/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.23/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.23/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.23/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.23/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.23/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.23/2.49  --sup_immed_triv                        [TrivRules]
% 15.23/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.23/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.23/2.49  --sup_immed_bw_main                     []
% 15.23/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.23/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.23/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.23/2.49  --sup_input_bw                          []
% 15.23/2.49  
% 15.23/2.49  ------ Combination Options
% 15.23/2.49  
% 15.23/2.49  --comb_res_mult                         3
% 15.23/2.49  --comb_sup_mult                         2
% 15.23/2.49  --comb_inst_mult                        10
% 15.23/2.49  
% 15.23/2.49  ------ Debug Options
% 15.23/2.49  
% 15.23/2.49  --dbg_backtrace                         false
% 15.23/2.49  --dbg_dump_prop_clauses                 false
% 15.23/2.49  --dbg_dump_prop_clauses_file            -
% 15.23/2.49  --dbg_out_stat                          false
% 15.23/2.49  
% 15.23/2.49  
% 15.23/2.49  
% 15.23/2.49  
% 15.23/2.49  ------ Proving...
% 15.23/2.49  
% 15.23/2.49  
% 15.23/2.49  % SZS status Theorem for theBenchmark.p
% 15.23/2.49  
% 15.23/2.49   Resolution empty clause
% 15.23/2.49  
% 15.23/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.23/2.49  
% 15.23/2.49  fof(f9,axiom,(
% 15.23/2.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f43,plain,(
% 15.23/2.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 15.23/2.49    inference(cnf_transformation,[],[f9])).
% 15.23/2.49  
% 15.23/2.49  fof(f1,axiom,(
% 15.23/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f21,plain,(
% 15.23/2.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 15.23/2.49    inference(ennf_transformation,[],[f1])).
% 15.23/2.49  
% 15.23/2.49  fof(f34,plain,(
% 15.23/2.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 15.23/2.49    inference(cnf_transformation,[],[f21])).
% 15.23/2.49  
% 15.23/2.49  fof(f10,axiom,(
% 15.23/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f29,plain,(
% 15.23/2.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 15.23/2.49    inference(nnf_transformation,[],[f10])).
% 15.23/2.49  
% 15.23/2.49  fof(f44,plain,(
% 15.23/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 15.23/2.49    inference(cnf_transformation,[],[f29])).
% 15.23/2.49  
% 15.23/2.49  fof(f8,axiom,(
% 15.23/2.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f42,plain,(
% 15.23/2.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 15.23/2.49    inference(cnf_transformation,[],[f8])).
% 15.23/2.49  
% 15.23/2.49  fof(f14,axiom,(
% 15.23/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f49,plain,(
% 15.23/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.23/2.49    inference(cnf_transformation,[],[f14])).
% 15.23/2.49  
% 15.23/2.49  fof(f12,axiom,(
% 15.23/2.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f47,plain,(
% 15.23/2.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.23/2.49    inference(cnf_transformation,[],[f12])).
% 15.23/2.49  
% 15.23/2.49  fof(f13,axiom,(
% 15.23/2.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f48,plain,(
% 15.23/2.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.23/2.49    inference(cnf_transformation,[],[f13])).
% 15.23/2.49  
% 15.23/2.49  fof(f59,plain,(
% 15.23/2.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.23/2.49    inference(definition_unfolding,[],[f47,f48])).
% 15.23/2.49  
% 15.23/2.49  fof(f60,plain,(
% 15.23/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 15.23/2.49    inference(definition_unfolding,[],[f49,f59])).
% 15.23/2.49  
% 15.23/2.49  fof(f6,axiom,(
% 15.23/2.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f40,plain,(
% 15.23/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 15.23/2.49    inference(cnf_transformation,[],[f6])).
% 15.23/2.49  
% 15.23/2.49  fof(f65,plain,(
% 15.23/2.49    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0) )),
% 15.23/2.49    inference(definition_unfolding,[],[f42,f60,f40])).
% 15.23/2.49  
% 15.23/2.49  fof(f5,axiom,(
% 15.23/2.49    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f39,plain,(
% 15.23/2.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 15.23/2.49    inference(cnf_transformation,[],[f5])).
% 15.23/2.49  
% 15.23/2.49  fof(f63,plain,(
% 15.23/2.49    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 15.23/2.49    inference(definition_unfolding,[],[f39,f60,f40,f40,f60])).
% 15.23/2.49  
% 15.23/2.49  fof(f7,axiom,(
% 15.23/2.49    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f41,plain,(
% 15.23/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 15.23/2.49    inference(cnf_transformation,[],[f7])).
% 15.23/2.49  
% 15.23/2.49  fof(f64,plain,(
% 15.23/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 15.23/2.49    inference(definition_unfolding,[],[f41,f40,f40])).
% 15.23/2.49  
% 15.23/2.49  fof(f4,axiom,(
% 15.23/2.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f38,plain,(
% 15.23/2.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 15.23/2.49    inference(cnf_transformation,[],[f4])).
% 15.23/2.49  
% 15.23/2.49  fof(f62,plain,(
% 15.23/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 15.23/2.49    inference(definition_unfolding,[],[f38,f40])).
% 15.23/2.49  
% 15.23/2.49  fof(f2,axiom,(
% 15.23/2.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f22,plain,(
% 15.23/2.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 15.23/2.49    inference(ennf_transformation,[],[f2])).
% 15.23/2.49  
% 15.23/2.49  fof(f36,plain,(
% 15.23/2.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 15.23/2.49    inference(cnf_transformation,[],[f22])).
% 15.23/2.49  
% 15.23/2.49  fof(f18,axiom,(
% 15.23/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f26,plain,(
% 15.23/2.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.23/2.49    inference(ennf_transformation,[],[f18])).
% 15.23/2.49  
% 15.23/2.49  fof(f27,plain,(
% 15.23/2.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.23/2.49    inference(flattening,[],[f26])).
% 15.23/2.49  
% 15.23/2.49  fof(f55,plain,(
% 15.23/2.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.23/2.49    inference(cnf_transformation,[],[f27])).
% 15.23/2.49  
% 15.23/2.49  fof(f17,axiom,(
% 15.23/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f25,plain,(
% 15.23/2.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.23/2.49    inference(ennf_transformation,[],[f17])).
% 15.23/2.49  
% 15.23/2.49  fof(f53,plain,(
% 15.23/2.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.23/2.49    inference(cnf_transformation,[],[f25])).
% 15.23/2.49  
% 15.23/2.49  fof(f16,axiom,(
% 15.23/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f30,plain,(
% 15.23/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.23/2.49    inference(nnf_transformation,[],[f16])).
% 15.23/2.49  
% 15.23/2.49  fof(f52,plain,(
% 15.23/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.23/2.49    inference(cnf_transformation,[],[f30])).
% 15.23/2.49  
% 15.23/2.49  fof(f11,axiom,(
% 15.23/2.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f23,plain,(
% 15.23/2.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 15.23/2.49    inference(ennf_transformation,[],[f11])).
% 15.23/2.49  
% 15.23/2.49  fof(f24,plain,(
% 15.23/2.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 15.23/2.49    inference(flattening,[],[f23])).
% 15.23/2.49  
% 15.23/2.49  fof(f46,plain,(
% 15.23/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 15.23/2.49    inference(cnf_transformation,[],[f24])).
% 15.23/2.49  
% 15.23/2.49  fof(f19,conjecture,(
% 15.23/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 15.23/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.23/2.49  
% 15.23/2.49  fof(f20,negated_conjecture,(
% 15.23/2.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 15.23/2.49    inference(negated_conjecture,[],[f19])).
% 15.23/2.49  
% 15.23/2.49  fof(f28,plain,(
% 15.23/2.49    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 15.23/2.49    inference(ennf_transformation,[],[f20])).
% 15.23/2.49  
% 15.23/2.49  fof(f32,plain,(
% 15.23/2.49    ( ! [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(sK1))) & v1_relat_1(sK1))) )),
% 15.23/2.49    introduced(choice_axiom,[])).
% 15.23/2.49  
% 15.23/2.49  fof(f31,plain,(
% 15.23/2.49    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 15.23/2.49    introduced(choice_axiom,[])).
% 15.23/2.49  
% 15.23/2.49  fof(f33,plain,(
% 15.23/2.49    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 15.23/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f32,f31])).
% 15.23/2.49  
% 15.23/2.49  fof(f58,plain,(
% 15.23/2.49    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 15.23/2.49    inference(cnf_transformation,[],[f33])).
% 15.23/2.49  
% 15.23/2.49  fof(f67,plain,(
% 15.23/2.49    ~r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))))),
% 15.23/2.49    inference(definition_unfolding,[],[f58,f40,f40])).
% 15.23/2.49  
% 15.23/2.49  fof(f56,plain,(
% 15.23/2.49    v1_relat_1(sK0)),
% 15.23/2.49    inference(cnf_transformation,[],[f33])).
% 15.23/2.49  
% 15.23/2.49  fof(f57,plain,(
% 15.23/2.49    v1_relat_1(sK1)),
% 15.23/2.49    inference(cnf_transformation,[],[f33])).
% 15.23/2.49  
% 15.23/2.49  cnf(c_8,plain,
% 15.23/2.49      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 15.23/2.49      inference(cnf_transformation,[],[f43]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_765,plain,
% 15.23/2.49      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_0,plain,
% 15.23/2.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 15.23/2.49      inference(cnf_transformation,[],[f34]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_770,plain,
% 15.23/2.49      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_1514,plain,
% 15.23/2.49      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_765,c_770]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_10,plain,
% 15.23/2.49      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 15.23/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_763,plain,
% 15.23/2.49      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_1526,plain,
% 15.23/2.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_1514,c_763]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_7,plain,
% 15.23/2.49      ( k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
% 15.23/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_1602,plain,
% 15.23/2.49      ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,X0))) = X0 ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_1526,c_7]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_5,plain,
% 15.23/2.49      ( r1_tarski(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
% 15.23/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_766,plain,
% 15.23/2.49      ( r1_tarski(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),k3_tarski(k2_enumset1(X1,X1,X1,X2))) = iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_7037,plain,
% 15.23/2.49      ( r1_tarski(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))))),X1) = iProver_top ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_1602,c_766]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_6,plain,
% 15.23/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 15.23/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_1605,plain,
% 15.23/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_1526,c_6]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_4,plain,
% 15.23/2.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 15.23/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_767,plain,
% 15.23/2.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2053,plain,
% 15.23/2.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_1605,c_767]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_1,plain,
% 15.23/2.49      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 15.23/2.49      inference(cnf_transformation,[],[f36]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_769,plain,
% 15.23/2.49      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 15.23/2.49      | r1_xboole_0(X0,X2) = iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2360,plain,
% 15.23/2.49      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = iProver_top ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2053,c_769]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2384,plain,
% 15.23/2.49      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = iProver_top ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2360,c_770]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2637,plain,
% 15.23/2.49      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2384,c_763]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_1588,plain,
% 15.23/2.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_6,c_1526]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2797,plain,
% 15.23/2.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2637,c_1588]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_7039,plain,
% 15.23/2.49      ( r1_tarski(k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X0))),X1) = iProver_top ),
% 15.23/2.49      inference(light_normalisation,[status(thm)],[c_7037,c_2797]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2762,plain,
% 15.23/2.49      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0))),X3)) = X0 ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_6,c_2637]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2803,plain,
% 15.23/2.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X0),X3)))) = X0 ),
% 15.23/2.49      inference(demodulation,[status(thm)],[c_2762,c_6]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2052,plain,
% 15.23/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_1605,c_6]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_5607,plain,
% 15.23/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),X3))) = k4_xboole_0(X0,X0) ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2803,c_2052]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2381,plain,
% 15.23/2.49      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = iProver_top ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_1526,c_2360]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2525,plain,
% 15.23/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2381,c_763]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_4464,plain,
% 15.23/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2525,c_1605]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_4462,plain,
% 15.23/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X3) ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2525,c_6]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_4521,plain,
% 15.23/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),X3) ),
% 15.23/2.49      inference(demodulation,[status(thm)],[c_4462,c_4464]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2524,plain,
% 15.23/2.49      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = iProver_top ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2381,c_770]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2660,plain,
% 15.23/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2524,c_763]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_4595,plain,
% 15.23/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X2,X0),X3)) = k4_xboole_0(X0,X1) ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2660,c_2637]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_5777,plain,
% 15.23/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 15.23/2.49      inference(light_normalisation,
% 15.23/2.49                [status(thm)],
% 15.23/2.49                [c_5607,c_4464,c_4521,c_4595]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_6053,plain,
% 15.23/2.49      ( k3_tarski(k2_enumset1(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X1) ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_5777,c_7]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_6138,plain,
% 15.23/2.49      ( k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) = k4_xboole_0(X0,X1) ),
% 15.23/2.49      inference(demodulation,[status(thm)],[c_6053,c_2525]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_7040,plain,
% 15.23/2.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 15.23/2.49      inference(demodulation,[status(thm)],[c_7039,c_6138]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_16,plain,
% 15.23/2.49      ( ~ r1_tarski(X0,X1)
% 15.23/2.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 15.23/2.49      | ~ v1_relat_1(X0)
% 15.23/2.49      | ~ v1_relat_1(X1) ),
% 15.23/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_15,plain,
% 15.23/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.23/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_13,plain,
% 15.23/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.23/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_109,plain,
% 15.23/2.49      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 15.23/2.49      | ~ r1_tarski(X0,X1)
% 15.23/2.49      | ~ v1_relat_1(X1) ),
% 15.23/2.49      inference(global_propositional_subsumption,
% 15.23/2.49                [status(thm)],
% 15.23/2.49                [c_16,c_15,c_13]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_110,plain,
% 15.23/2.49      ( ~ r1_tarski(X0,X1)
% 15.23/2.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 15.23/2.49      | ~ v1_relat_1(X1) ),
% 15.23/2.49      inference(renaming,[status(thm)],[c_109]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_757,plain,
% 15.23/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.23/2.49      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 15.23/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_110]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_2237,plain,
% 15.23/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.23/2.49      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) = iProver_top ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_1526,c_769]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_11,plain,
% 15.23/2.49      ( ~ r1_tarski(X0,X1)
% 15.23/2.49      | r1_tarski(X0,k4_xboole_0(X1,X2))
% 15.23/2.49      | ~ r1_xboole_0(X0,X2) ),
% 15.23/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_762,plain,
% 15.23/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.23/2.49      | r1_tarski(X0,k4_xboole_0(X1,X2)) = iProver_top
% 15.23/2.49      | r1_xboole_0(X0,X2) != iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_18,negated_conjecture,
% 15.23/2.49      ( ~ r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) ),
% 15.23/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_761,plain,
% 15.23/2.49      ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) != iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_5008,plain,
% 15.23/2.49      ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0)) != iProver_top
% 15.23/2.49      | r1_xboole_0(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) != iProver_top ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_762,c_761]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_20,negated_conjecture,
% 15.23/2.49      ( v1_relat_1(sK0) ),
% 15.23/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_21,plain,
% 15.23/2.49      ( v1_relat_1(sK0) = iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_23,plain,
% 15.23/2.49      ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) != iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_791,plain,
% 15.23/2.49      ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))))
% 15.23/2.49      | ~ r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0))
% 15.23/2.49      | ~ r1_xboole_0(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
% 15.23/2.49      inference(instantiation,[status(thm)],[c_11]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_792,plain,
% 15.23/2.49      ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) = iProver_top
% 15.23/2.49      | r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0)) != iProver_top
% 15.23/2.49      | r1_xboole_0(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) != iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_809,plain,
% 15.23/2.49      ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
% 15.23/2.49      | r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0))
% 15.23/2.49      | ~ v1_relat_1(sK0) ),
% 15.23/2.49      inference(instantiation,[status(thm)],[c_110]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_810,plain,
% 15.23/2.49      ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) != iProver_top
% 15.23/2.49      | r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0)) = iProver_top
% 15.23/2.49      | v1_relat_1(sK0) != iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_809]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_847,plain,
% 15.23/2.49      ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
% 15.23/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_848,plain,
% 15.23/2.49      ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) = iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_6007,plain,
% 15.23/2.49      ( r1_xboole_0(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) != iProver_top ),
% 15.23/2.49      inference(global_propositional_subsumption,
% 15.23/2.49                [status(thm)],
% 15.23/2.49                [c_5008,c_21,c_23,c_792,c_810,c_848]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_51624,plain,
% 15.23/2.49      ( r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1)) != iProver_top ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_2237,c_6007]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_51898,plain,
% 15.23/2.49      ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) != iProver_top
% 15.23/2.49      | v1_relat_1(sK1) != iProver_top ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_757,c_51624]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_19,negated_conjecture,
% 15.23/2.49      ( v1_relat_1(sK1) ),
% 15.23/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_22,plain,
% 15.23/2.49      ( v1_relat_1(sK1) = iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_18976,plain,
% 15.23/2.49      ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
% 15.23/2.49      | r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1))
% 15.23/2.49      | ~ v1_relat_1(sK1) ),
% 15.23/2.49      inference(instantiation,[status(thm)],[c_110]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_18977,plain,
% 15.23/2.49      ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) != iProver_top
% 15.23/2.49      | r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1)) = iProver_top
% 15.23/2.49      | v1_relat_1(sK1) != iProver_top ),
% 15.23/2.49      inference(predicate_to_equality,[status(thm)],[c_18976]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_56136,plain,
% 15.23/2.49      ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) != iProver_top ),
% 15.23/2.49      inference(global_propositional_subsumption,
% 15.23/2.49                [status(thm)],
% 15.23/2.49                [c_51898,c_22,c_18977,c_51624]) ).
% 15.23/2.49  
% 15.23/2.49  cnf(c_56140,plain,
% 15.23/2.49      ( $false ),
% 15.23/2.49      inference(superposition,[status(thm)],[c_7040,c_56136]) ).
% 15.23/2.49  
% 15.23/2.49  
% 15.23/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.23/2.49  
% 15.23/2.49  ------                               Statistics
% 15.23/2.49  
% 15.23/2.49  ------ General
% 15.23/2.49  
% 15.23/2.49  abstr_ref_over_cycles:                  0
% 15.23/2.49  abstr_ref_under_cycles:                 0
% 15.23/2.49  gc_basic_clause_elim:                   0
% 15.23/2.49  forced_gc_time:                         0
% 15.23/2.49  parsing_time:                           0.008
% 15.23/2.49  unif_index_cands_time:                  0.
% 15.23/2.49  unif_index_add_time:                    0.
% 15.23/2.49  orderings_time:                         0.
% 15.23/2.49  out_proof_time:                         0.012
% 15.23/2.49  total_time:                             1.614
% 15.23/2.49  num_of_symbols:                         44
% 15.23/2.49  num_of_terms:                           77267
% 15.23/2.49  
% 15.23/2.49  ------ Preprocessing
% 15.23/2.49  
% 15.23/2.49  num_of_splits:                          0
% 15.23/2.49  num_of_split_atoms:                     0
% 15.23/2.49  num_of_reused_defs:                     0
% 15.23/2.49  num_eq_ax_congr_red:                    8
% 15.23/2.49  num_of_sem_filtered_clauses:            1
% 15.23/2.49  num_of_subtypes:                        0
% 15.23/2.49  monotx_restored_types:                  0
% 15.23/2.49  sat_num_of_epr_types:                   0
% 15.23/2.49  sat_num_of_non_cyclic_types:            0
% 15.23/2.49  sat_guarded_non_collapsed_types:        0
% 15.23/2.49  num_pure_diseq_elim:                    0
% 15.23/2.49  simp_replaced_by:                       0
% 15.23/2.49  res_preprocessed:                       99
% 15.23/2.49  prep_upred:                             0
% 15.23/2.49  prep_unflattend:                        0
% 15.23/2.49  smt_new_axioms:                         0
% 15.23/2.49  pred_elim_cands:                        3
% 15.23/2.49  pred_elim:                              1
% 15.23/2.49  pred_elim_cl:                           2
% 15.23/2.49  pred_elim_cycles:                       3
% 15.23/2.49  merged_defs:                            10
% 15.23/2.49  merged_defs_ncl:                        0
% 15.23/2.49  bin_hyper_res:                          11
% 15.23/2.49  prep_cycles:                            4
% 15.23/2.49  pred_elim_time:                         0.
% 15.23/2.49  splitting_time:                         0.
% 15.23/2.49  sem_filter_time:                        0.
% 15.23/2.49  monotx_time:                            0.
% 15.23/2.49  subtype_inf_time:                       0.
% 15.23/2.49  
% 15.23/2.49  ------ Problem properties
% 15.23/2.49  
% 15.23/2.49  clauses:                                19
% 15.23/2.49  conjectures:                            3
% 15.23/2.49  epr:                                    4
% 15.23/2.49  horn:                                   19
% 15.23/2.49  ground:                                 3
% 15.23/2.49  unary:                                  10
% 15.23/2.49  binary:                                 5
% 15.23/2.49  lits:                                   32
% 15.23/2.49  lits_eq:                                6
% 15.23/2.49  fd_pure:                                0
% 15.23/2.49  fd_pseudo:                              0
% 15.23/2.49  fd_cond:                                0
% 15.23/2.49  fd_pseudo_cond:                         0
% 15.23/2.49  ac_symbols:                             0
% 15.23/2.49  
% 15.23/2.49  ------ Propositional Solver
% 15.23/2.49  
% 15.23/2.49  prop_solver_calls:                      33
% 15.23/2.49  prop_fast_solver_calls:                 632
% 15.23/2.49  smt_solver_calls:                       0
% 15.23/2.49  smt_fast_solver_calls:                  0
% 15.23/2.49  prop_num_of_clauses:                    14183
% 15.23/2.49  prop_preprocess_simplified:             16736
% 15.23/2.49  prop_fo_subsumed:                       4
% 15.23/2.49  prop_solver_time:                       0.
% 15.23/2.49  smt_solver_time:                        0.
% 15.23/2.49  smt_fast_solver_time:                   0.
% 15.23/2.49  prop_fast_solver_time:                  0.
% 15.23/2.49  prop_unsat_core_time:                   0.
% 15.23/2.49  
% 15.23/2.49  ------ QBF
% 15.23/2.49  
% 15.23/2.49  qbf_q_res:                              0
% 15.23/2.49  qbf_num_tautologies:                    0
% 15.23/2.49  qbf_prep_cycles:                        0
% 15.23/2.49  
% 15.23/2.49  ------ BMC1
% 15.23/2.49  
% 15.23/2.49  bmc1_current_bound:                     -1
% 15.23/2.49  bmc1_last_solved_bound:                 -1
% 15.23/2.49  bmc1_unsat_core_size:                   -1
% 15.23/2.49  bmc1_unsat_core_parents_size:           -1
% 15.23/2.49  bmc1_merge_next_fun:                    0
% 15.23/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.23/2.49  
% 15.23/2.49  ------ Instantiation
% 15.23/2.49  
% 15.23/2.49  inst_num_of_clauses:                    2173
% 15.23/2.49  inst_num_in_passive:                    672
% 15.23/2.49  inst_num_in_active:                     884
% 15.23/2.49  inst_num_in_unprocessed:                617
% 15.23/2.49  inst_num_of_loops:                      930
% 15.23/2.49  inst_num_of_learning_restarts:          0
% 15.23/2.49  inst_num_moves_active_passive:          42
% 15.23/2.49  inst_lit_activity:                      0
% 15.23/2.49  inst_lit_activity_moves:                0
% 15.23/2.49  inst_num_tautologies:                   0
% 15.23/2.49  inst_num_prop_implied:                  0
% 15.23/2.49  inst_num_existing_simplified:           0
% 15.23/2.49  inst_num_eq_res_simplified:             0
% 15.23/2.49  inst_num_child_elim:                    0
% 15.23/2.49  inst_num_of_dismatching_blockings:      2079
% 15.23/2.49  inst_num_of_non_proper_insts:           3312
% 15.23/2.49  inst_num_of_duplicates:                 0
% 15.23/2.49  inst_inst_num_from_inst_to_res:         0
% 15.23/2.49  inst_dismatching_checking_time:         0.
% 15.23/2.49  
% 15.23/2.49  ------ Resolution
% 15.23/2.49  
% 15.23/2.49  res_num_of_clauses:                     0
% 15.23/2.49  res_num_in_passive:                     0
% 15.23/2.49  res_num_in_active:                      0
% 15.23/2.49  res_num_of_loops:                       103
% 15.23/2.49  res_forward_subset_subsumed:            244
% 15.23/2.49  res_backward_subset_subsumed:           6
% 15.23/2.49  res_forward_subsumed:                   0
% 15.23/2.49  res_backward_subsumed:                  0
% 15.23/2.49  res_forward_subsumption_resolution:     0
% 15.23/2.49  res_backward_subsumption_resolution:    0
% 15.23/2.49  res_clause_to_clause_subsumption:       149967
% 15.23/2.49  res_orphan_elimination:                 0
% 15.23/2.49  res_tautology_del:                      413
% 15.23/2.49  res_num_eq_res_simplified:              0
% 15.23/2.49  res_num_sel_changes:                    0
% 15.23/2.49  res_moves_from_active_to_pass:          0
% 15.23/2.49  
% 15.23/2.49  ------ Superposition
% 15.23/2.49  
% 15.23/2.49  sup_time_total:                         0.
% 15.23/2.49  sup_time_generating:                    0.
% 15.23/2.49  sup_time_sim_full:                      0.
% 15.23/2.49  sup_time_sim_immed:                     0.
% 15.23/2.49  
% 15.23/2.49  sup_num_of_clauses:                     2800
% 15.23/2.49  sup_num_in_active:                      174
% 15.23/2.49  sup_num_in_passive:                     2626
% 15.23/2.49  sup_num_of_loops:                       184
% 15.23/2.49  sup_fw_superposition:                   15244
% 15.23/2.49  sup_bw_superposition:                   9343
% 15.23/2.49  sup_immediate_simplified:               9886
% 15.23/2.49  sup_given_eliminated:                   4
% 15.23/2.49  comparisons_done:                       0
% 15.23/2.49  comparisons_avoided:                    0
% 15.23/2.49  
% 15.23/2.49  ------ Simplifications
% 15.23/2.49  
% 15.23/2.49  
% 15.23/2.49  sim_fw_subset_subsumed:                 7
% 15.23/2.49  sim_bw_subset_subsumed:                 2
% 15.23/2.49  sim_fw_subsumed:                        2807
% 15.23/2.49  sim_bw_subsumed:                        93
% 15.23/2.49  sim_fw_subsumption_res:                 0
% 15.23/2.49  sim_bw_subsumption_res:                 0
% 15.23/2.49  sim_tautology_del:                      68
% 15.23/2.49  sim_eq_tautology_del:                   1378
% 15.23/2.49  sim_eq_res_simp:                        29
% 15.23/2.49  sim_fw_demodulated:                     7891
% 15.23/2.49  sim_bw_demodulated:                     130
% 15.23/2.49  sim_light_normalised:                   3692
% 15.23/2.49  sim_joinable_taut:                      0
% 15.23/2.49  sim_joinable_simp:                      0
% 15.23/2.49  sim_ac_normalised:                      0
% 15.23/2.49  sim_smt_subsumption:                    0
% 15.23/2.49  
%------------------------------------------------------------------------------
