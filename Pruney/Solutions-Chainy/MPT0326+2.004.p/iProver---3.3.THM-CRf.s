%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:55 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 379 expanded)
%              Number of clauses        :   61 ( 134 expanded)
%              Number of leaves         :   14 (  87 expanded)
%              Depth                    :   17
%              Number of atoms          :  295 (1303 expanded)
%              Number of equality atoms :  104 ( 222 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
     => ( ~ r1_tarski(sK4,sK6)
        & ( r1_tarski(k2_zfmisc_1(sK4,X0),k2_zfmisc_1(sK6,sK5))
          | r1_tarski(k2_zfmisc_1(X0,sK4),k2_zfmisc_1(sK5,sK6)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r1_tarski(X1,X3)
            & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(sK3,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_tarski(sK4,sK6)
    & ( r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5))
      | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6)) )
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f18,f31,f30])).

fof(f48,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5))
    | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6)) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ~ r1_tarski(sK4,sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f19])).

fof(f33,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f26])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6))
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_697,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_705,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1665,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top
    | r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_705])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
    | k2_zfmisc_1(X0,X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_699,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1869,plain,
    ( k2_zfmisc_1(sK4,sK3) = k1_xboole_0
    | r1_tarski(sK4,sK6) = iProver_top
    | r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_699])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK4,sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_32,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_35,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_187,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_188,plain,
    ( r2_hidden(sK0(sK3),sK3) ),
    inference(unflattening,[status(thm)],[c_187])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_799,plain,
    ( r1_tarski(sK4,sK6)
    | r2_hidden(sK1(sK4,sK6),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_802,plain,
    ( ~ r1_tarski(sK3,X0)
    | r2_hidden(sK0(sK3),X0)
    | ~ r2_hidden(sK0(sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1058,plain,
    ( ~ r1_tarski(sK3,k3_xboole_0(X0,X1))
    | r2_hidden(sK0(sK3),k3_xboole_0(X0,X1))
    | ~ r2_hidden(sK0(sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1061,plain,
    ( ~ r1_tarski(sK3,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | r2_hidden(sK0(sK3),k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK0(sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1059,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK0(sK3),k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1065,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK0(sK3),k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_706,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_707,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1102,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_707])).

cnf(c_1103,plain,
    ( r1_tarski(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1102])).

cnf(c_1105,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_835,plain,
    ( ~ r1_tarski(sK4,X0)
    | r2_hidden(sK1(sK4,sK6),X0)
    | ~ r2_hidden(sK1(sK4,sK6),sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1111,plain,
    ( ~ r1_tarski(sK4,k3_xboole_0(X0,X1))
    | r2_hidden(sK1(sK4,sK6),k3_xboole_0(X0,X1))
    | ~ r2_hidden(sK1(sK4,sK6),sK4) ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_1114,plain,
    ( ~ r1_tarski(sK4,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | r2_hidden(sK1(sK4,sK6),k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(sK1(sK4,sK6),sK4) ),
    inference(instantiation,[status(thm)],[c_1111])).

cnf(c_1112,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK1(sK4,sK6),k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1118,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK1(sK4,sK6),k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_391,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_925,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_1356,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k3_xboole_0(X2,X3))
    | k3_xboole_0(X2,X3) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_1363,plain,
    ( r1_tarski(sK3,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_972,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X2)
    | X2 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_1434,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,k3_xboole_0(X2,X3))
    | k3_xboole_0(X2,X3) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_1436,plain,
    ( r1_tarski(sK4,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_1568,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top
    | r1_tarski(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_699])).

cnf(c_18,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19,plain,
    ( r1_tarski(sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))
    | k2_zfmisc_1(X2,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_807,plain,
    ( ~ r1_tarski(k2_zfmisc_1(X0,sK4),k2_zfmisc_1(X1,sK6))
    | r1_tarski(sK4,sK6)
    | k2_zfmisc_1(X0,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_865,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6))
    | r1_tarski(sK4,sK6)
    | k2_zfmisc_1(sK3,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_866,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6)) != iProver_top
    | r1_tarski(sK4,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_865])).

cnf(c_1746,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top
    | k2_zfmisc_1(sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1568,c_18,c_19,c_866])).

cnf(c_1747,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1746])).

cnf(c_1753,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
    | k2_zfmisc_1(sK4,sK3) = k1_xboole_0
    | r1_tarski(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_699])).

cnf(c_1769,plain,
    ( r1_tarski(sK4,sK6)
    | k2_zfmisc_1(sK3,sK4) = k1_xboole_0
    | k2_zfmisc_1(sK4,sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1753])).

cnf(c_1902,plain,
    ( k2_zfmisc_1(sK4,sK3) = k1_xboole_0
    | k2_zfmisc_1(sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1753,c_14,c_1769])).

cnf(c_1903,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
    | k2_zfmisc_1(sK4,sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1902])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1908,plain,
    ( k2_zfmisc_1(sK4,sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1903,c_11])).

cnf(c_2039,plain,
    ( k2_zfmisc_1(sK4,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1869,c_14,c_32,c_35,c_188,c_799,c_1061,c_1065,c_1105,c_1114,c_1118,c_1363,c_1436,c_1908])).

cnf(c_2055,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2039,c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2055,c_1436,c_1363,c_1118,c_1114,c_1105,c_1065,c_1061,c_799,c_188,c_35,c_32,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:13:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 1.55/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/0.99  
% 1.55/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.55/0.99  
% 1.55/0.99  ------  iProver source info
% 1.55/0.99  
% 1.55/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.55/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.55/0.99  git: non_committed_changes: false
% 1.55/0.99  git: last_make_outside_of_git: false
% 1.55/0.99  
% 1.55/0.99  ------ 
% 1.55/0.99  
% 1.55/0.99  ------ Input Options
% 1.55/0.99  
% 1.55/0.99  --out_options                           all
% 1.55/0.99  --tptp_safe_out                         true
% 1.55/0.99  --problem_path                          ""
% 1.55/0.99  --include_path                          ""
% 1.55/0.99  --clausifier                            res/vclausify_rel
% 1.55/0.99  --clausifier_options                    --mode clausify
% 1.55/0.99  --stdin                                 false
% 1.55/0.99  --stats_out                             all
% 1.55/0.99  
% 1.55/0.99  ------ General Options
% 1.55/0.99  
% 1.55/0.99  --fof                                   false
% 1.55/0.99  --time_out_real                         305.
% 1.55/0.99  --time_out_virtual                      -1.
% 1.55/0.99  --symbol_type_check                     false
% 1.55/0.99  --clausify_out                          false
% 1.55/0.99  --sig_cnt_out                           false
% 1.55/0.99  --trig_cnt_out                          false
% 1.55/0.99  --trig_cnt_out_tolerance                1.
% 1.55/0.99  --trig_cnt_out_sk_spl                   false
% 1.55/0.99  --abstr_cl_out                          false
% 1.55/0.99  
% 1.55/0.99  ------ Global Options
% 1.55/0.99  
% 1.55/0.99  --schedule                              default
% 1.55/0.99  --add_important_lit                     false
% 1.55/0.99  --prop_solver_per_cl                    1000
% 1.55/0.99  --min_unsat_core                        false
% 1.55/0.99  --soft_assumptions                      false
% 1.55/0.99  --soft_lemma_size                       3
% 1.55/0.99  --prop_impl_unit_size                   0
% 1.55/0.99  --prop_impl_unit                        []
% 1.55/0.99  --share_sel_clauses                     true
% 1.55/0.99  --reset_solvers                         false
% 1.55/0.99  --bc_imp_inh                            [conj_cone]
% 1.55/0.99  --conj_cone_tolerance                   3.
% 1.55/0.99  --extra_neg_conj                        none
% 1.55/0.99  --large_theory_mode                     true
% 1.55/0.99  --prolific_symb_bound                   200
% 1.55/0.99  --lt_threshold                          2000
% 1.55/0.99  --clause_weak_htbl                      true
% 1.55/0.99  --gc_record_bc_elim                     false
% 1.55/0.99  
% 1.55/0.99  ------ Preprocessing Options
% 1.55/0.99  
% 1.55/0.99  --preprocessing_flag                    true
% 1.55/0.99  --time_out_prep_mult                    0.1
% 1.55/0.99  --splitting_mode                        input
% 1.55/0.99  --splitting_grd                         true
% 1.55/0.99  --splitting_cvd                         false
% 1.55/0.99  --splitting_cvd_svl                     false
% 1.55/0.99  --splitting_nvd                         32
% 1.55/0.99  --sub_typing                            true
% 1.55/0.99  --prep_gs_sim                           true
% 1.55/0.99  --prep_unflatten                        true
% 1.55/0.99  --prep_res_sim                          true
% 1.55/0.99  --prep_upred                            true
% 1.55/0.99  --prep_sem_filter                       exhaustive
% 1.55/0.99  --prep_sem_filter_out                   false
% 1.55/0.99  --pred_elim                             true
% 1.55/0.99  --res_sim_input                         true
% 1.55/0.99  --eq_ax_congr_red                       true
% 1.55/0.99  --pure_diseq_elim                       true
% 1.55/0.99  --brand_transform                       false
% 1.55/0.99  --non_eq_to_eq                          false
% 1.55/0.99  --prep_def_merge                        true
% 1.55/0.99  --prep_def_merge_prop_impl              false
% 1.55/0.99  --prep_def_merge_mbd                    true
% 1.55/0.99  --prep_def_merge_tr_red                 false
% 1.55/0.99  --prep_def_merge_tr_cl                  false
% 1.55/0.99  --smt_preprocessing                     true
% 1.55/0.99  --smt_ac_axioms                         fast
% 1.55/0.99  --preprocessed_out                      false
% 1.55/0.99  --preprocessed_stats                    false
% 1.55/0.99  
% 1.55/0.99  ------ Abstraction refinement Options
% 1.55/0.99  
% 1.55/0.99  --abstr_ref                             []
% 1.55/0.99  --abstr_ref_prep                        false
% 1.55/0.99  --abstr_ref_until_sat                   false
% 1.55/0.99  --abstr_ref_sig_restrict                funpre
% 1.55/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.55/0.99  --abstr_ref_under                       []
% 1.55/0.99  
% 1.55/0.99  ------ SAT Options
% 1.55/0.99  
% 1.55/0.99  --sat_mode                              false
% 1.55/0.99  --sat_fm_restart_options                ""
% 1.55/0.99  --sat_gr_def                            false
% 1.55/0.99  --sat_epr_types                         true
% 1.55/0.99  --sat_non_cyclic_types                  false
% 1.55/0.99  --sat_finite_models                     false
% 1.55/0.99  --sat_fm_lemmas                         false
% 1.55/0.99  --sat_fm_prep                           false
% 1.55/0.99  --sat_fm_uc_incr                        true
% 1.55/0.99  --sat_out_model                         small
% 1.55/0.99  --sat_out_clauses                       false
% 1.55/0.99  
% 1.55/0.99  ------ QBF Options
% 1.55/0.99  
% 1.55/0.99  --qbf_mode                              false
% 1.55/0.99  --qbf_elim_univ                         false
% 1.55/0.99  --qbf_dom_inst                          none
% 1.55/0.99  --qbf_dom_pre_inst                      false
% 1.55/0.99  --qbf_sk_in                             false
% 1.55/0.99  --qbf_pred_elim                         true
% 1.55/0.99  --qbf_split                             512
% 1.55/0.99  
% 1.55/0.99  ------ BMC1 Options
% 1.55/0.99  
% 1.55/0.99  --bmc1_incremental                      false
% 1.55/0.99  --bmc1_axioms                           reachable_all
% 1.55/0.99  --bmc1_min_bound                        0
% 1.55/0.99  --bmc1_max_bound                        -1
% 1.55/0.99  --bmc1_max_bound_default                -1
% 1.55/0.99  --bmc1_symbol_reachability              true
% 1.55/0.99  --bmc1_property_lemmas                  false
% 1.55/0.99  --bmc1_k_induction                      false
% 1.55/0.99  --bmc1_non_equiv_states                 false
% 1.55/0.99  --bmc1_deadlock                         false
% 1.55/0.99  --bmc1_ucm                              false
% 1.55/0.99  --bmc1_add_unsat_core                   none
% 1.55/0.99  --bmc1_unsat_core_children              false
% 1.55/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.55/0.99  --bmc1_out_stat                         full
% 1.55/0.99  --bmc1_ground_init                      false
% 1.55/0.99  --bmc1_pre_inst_next_state              false
% 1.55/0.99  --bmc1_pre_inst_state                   false
% 1.55/0.99  --bmc1_pre_inst_reach_state             false
% 1.55/0.99  --bmc1_out_unsat_core                   false
% 1.55/0.99  --bmc1_aig_witness_out                  false
% 1.55/0.99  --bmc1_verbose                          false
% 1.55/0.99  --bmc1_dump_clauses_tptp                false
% 1.55/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.55/0.99  --bmc1_dump_file                        -
% 1.55/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.55/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.55/0.99  --bmc1_ucm_extend_mode                  1
% 1.55/0.99  --bmc1_ucm_init_mode                    2
% 1.55/0.99  --bmc1_ucm_cone_mode                    none
% 1.55/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.55/0.99  --bmc1_ucm_relax_model                  4
% 1.55/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.55/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.55/0.99  --bmc1_ucm_layered_model                none
% 1.55/0.99  --bmc1_ucm_max_lemma_size               10
% 1.55/0.99  
% 1.55/0.99  ------ AIG Options
% 1.55/0.99  
% 1.55/0.99  --aig_mode                              false
% 1.55/0.99  
% 1.55/0.99  ------ Instantiation Options
% 1.55/0.99  
% 1.55/0.99  --instantiation_flag                    true
% 1.55/0.99  --inst_sos_flag                         false
% 1.55/0.99  --inst_sos_phase                        true
% 1.55/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.55/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.55/0.99  --inst_lit_sel_side                     num_symb
% 1.55/0.99  --inst_solver_per_active                1400
% 1.55/0.99  --inst_solver_calls_frac                1.
% 1.55/0.99  --inst_passive_queue_type               priority_queues
% 1.55/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.55/0.99  --inst_passive_queues_freq              [25;2]
% 1.55/0.99  --inst_dismatching                      true
% 1.55/0.99  --inst_eager_unprocessed_to_passive     true
% 1.55/0.99  --inst_prop_sim_given                   true
% 1.55/0.99  --inst_prop_sim_new                     false
% 1.55/0.99  --inst_subs_new                         false
% 1.55/0.99  --inst_eq_res_simp                      false
% 1.55/0.99  --inst_subs_given                       false
% 1.55/0.99  --inst_orphan_elimination               true
% 1.55/0.99  --inst_learning_loop_flag               true
% 1.55/0.99  --inst_learning_start                   3000
% 1.55/0.99  --inst_learning_factor                  2
% 1.55/0.99  --inst_start_prop_sim_after_learn       3
% 1.55/0.99  --inst_sel_renew                        solver
% 1.55/0.99  --inst_lit_activity_flag                true
% 1.55/0.99  --inst_restr_to_given                   false
% 1.55/0.99  --inst_activity_threshold               500
% 1.55/0.99  --inst_out_proof                        true
% 1.55/0.99  
% 1.55/0.99  ------ Resolution Options
% 1.55/0.99  
% 1.55/0.99  --resolution_flag                       true
% 1.55/0.99  --res_lit_sel                           adaptive
% 1.55/0.99  --res_lit_sel_side                      none
% 1.55/0.99  --res_ordering                          kbo
% 1.55/0.99  --res_to_prop_solver                    active
% 1.55/0.99  --res_prop_simpl_new                    false
% 1.55/0.99  --res_prop_simpl_given                  true
% 1.55/0.99  --res_passive_queue_type                priority_queues
% 1.55/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.55/0.99  --res_passive_queues_freq               [15;5]
% 1.55/0.99  --res_forward_subs                      full
% 1.55/0.99  --res_backward_subs                     full
% 1.55/0.99  --res_forward_subs_resolution           true
% 1.55/0.99  --res_backward_subs_resolution          true
% 1.55/0.99  --res_orphan_elimination                true
% 1.55/0.99  --res_time_limit                        2.
% 1.55/0.99  --res_out_proof                         true
% 1.55/0.99  
% 1.55/0.99  ------ Superposition Options
% 1.55/0.99  
% 1.55/0.99  --superposition_flag                    true
% 1.55/0.99  --sup_passive_queue_type                priority_queues
% 1.55/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.55/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.55/0.99  --demod_completeness_check              fast
% 1.55/0.99  --demod_use_ground                      true
% 1.55/0.99  --sup_to_prop_solver                    passive
% 1.55/0.99  --sup_prop_simpl_new                    true
% 1.55/0.99  --sup_prop_simpl_given                  true
% 1.55/0.99  --sup_fun_splitting                     false
% 1.55/0.99  --sup_smt_interval                      50000
% 1.55/0.99  
% 1.55/0.99  ------ Superposition Simplification Setup
% 1.55/0.99  
% 1.55/0.99  --sup_indices_passive                   []
% 1.55/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.55/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/0.99  --sup_full_bw                           [BwDemod]
% 1.55/0.99  --sup_immed_triv                        [TrivRules]
% 1.55/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.55/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/0.99  --sup_immed_bw_main                     []
% 1.55/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.55/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/0.99  
% 1.55/0.99  ------ Combination Options
% 1.55/0.99  
% 1.55/0.99  --comb_res_mult                         3
% 1.55/0.99  --comb_sup_mult                         2
% 1.55/0.99  --comb_inst_mult                        10
% 1.55/0.99  
% 1.55/0.99  ------ Debug Options
% 1.55/0.99  
% 1.55/0.99  --dbg_backtrace                         false
% 1.55/0.99  --dbg_dump_prop_clauses                 false
% 1.55/0.99  --dbg_dump_prop_clauses_file            -
% 1.55/0.99  --dbg_out_stat                          false
% 1.55/0.99  ------ Parsing...
% 1.55/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.55/0.99  
% 1.55/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.55/0.99  
% 1.55/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.55/0.99  
% 1.55/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.55/0.99  ------ Proving...
% 1.55/0.99  ------ Problem Properties 
% 1.55/0.99  
% 1.55/0.99  
% 1.55/0.99  clauses                                 16
% 1.55/0.99  conjectures                             2
% 1.55/0.99  EPR                                     2
% 1.55/0.99  Horn                                    10
% 1.55/0.99  unary                                   5
% 1.55/0.99  binary                                  7
% 1.55/0.99  lits                                    31
% 1.55/0.99  lits eq                                 10
% 1.55/0.99  fd_pure                                 0
% 1.55/0.99  fd_pseudo                               0
% 1.55/0.99  fd_cond                                 1
% 1.55/0.99  fd_pseudo_cond                          0
% 1.55/0.99  AC symbols                              0
% 1.55/0.99  
% 1.55/0.99  ------ Schedule dynamic 5 is on 
% 1.55/0.99  
% 1.55/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.55/0.99  
% 1.55/0.99  
% 1.55/0.99  ------ 
% 1.55/0.99  Current options:
% 1.55/0.99  ------ 
% 1.55/0.99  
% 1.55/0.99  ------ Input Options
% 1.55/0.99  
% 1.55/0.99  --out_options                           all
% 1.55/0.99  --tptp_safe_out                         true
% 1.55/0.99  --problem_path                          ""
% 1.55/0.99  --include_path                          ""
% 1.55/0.99  --clausifier                            res/vclausify_rel
% 1.55/0.99  --clausifier_options                    --mode clausify
% 1.55/0.99  --stdin                                 false
% 1.55/0.99  --stats_out                             all
% 1.55/0.99  
% 1.55/0.99  ------ General Options
% 1.55/0.99  
% 1.55/0.99  --fof                                   false
% 1.55/0.99  --time_out_real                         305.
% 1.55/0.99  --time_out_virtual                      -1.
% 1.55/0.99  --symbol_type_check                     false
% 1.55/0.99  --clausify_out                          false
% 1.55/0.99  --sig_cnt_out                           false
% 1.55/0.99  --trig_cnt_out                          false
% 1.55/0.99  --trig_cnt_out_tolerance                1.
% 1.55/0.99  --trig_cnt_out_sk_spl                   false
% 1.55/0.99  --abstr_cl_out                          false
% 1.55/0.99  
% 1.55/0.99  ------ Global Options
% 1.55/0.99  
% 1.55/0.99  --schedule                              default
% 1.55/0.99  --add_important_lit                     false
% 1.55/0.99  --prop_solver_per_cl                    1000
% 1.55/0.99  --min_unsat_core                        false
% 1.55/0.99  --soft_assumptions                      false
% 1.55/0.99  --soft_lemma_size                       3
% 1.55/0.99  --prop_impl_unit_size                   0
% 1.55/0.99  --prop_impl_unit                        []
% 1.55/0.99  --share_sel_clauses                     true
% 1.55/0.99  --reset_solvers                         false
% 1.55/0.99  --bc_imp_inh                            [conj_cone]
% 1.55/0.99  --conj_cone_tolerance                   3.
% 1.55/0.99  --extra_neg_conj                        none
% 1.55/0.99  --large_theory_mode                     true
% 1.55/0.99  --prolific_symb_bound                   200
% 1.55/0.99  --lt_threshold                          2000
% 1.55/0.99  --clause_weak_htbl                      true
% 1.55/0.99  --gc_record_bc_elim                     false
% 1.55/0.99  
% 1.55/0.99  ------ Preprocessing Options
% 1.55/0.99  
% 1.55/0.99  --preprocessing_flag                    true
% 1.55/0.99  --time_out_prep_mult                    0.1
% 1.55/0.99  --splitting_mode                        input
% 1.55/0.99  --splitting_grd                         true
% 1.55/0.99  --splitting_cvd                         false
% 1.55/0.99  --splitting_cvd_svl                     false
% 1.55/0.99  --splitting_nvd                         32
% 1.55/0.99  --sub_typing                            true
% 1.55/0.99  --prep_gs_sim                           true
% 1.55/0.99  --prep_unflatten                        true
% 1.55/0.99  --prep_res_sim                          true
% 1.55/0.99  --prep_upred                            true
% 1.55/0.99  --prep_sem_filter                       exhaustive
% 1.55/0.99  --prep_sem_filter_out                   false
% 1.55/0.99  --pred_elim                             true
% 1.55/0.99  --res_sim_input                         true
% 1.55/0.99  --eq_ax_congr_red                       true
% 1.55/0.99  --pure_diseq_elim                       true
% 1.55/0.99  --brand_transform                       false
% 1.55/0.99  --non_eq_to_eq                          false
% 1.55/0.99  --prep_def_merge                        true
% 1.55/0.99  --prep_def_merge_prop_impl              false
% 1.55/0.99  --prep_def_merge_mbd                    true
% 1.55/0.99  --prep_def_merge_tr_red                 false
% 1.55/0.99  --prep_def_merge_tr_cl                  false
% 1.55/0.99  --smt_preprocessing                     true
% 1.55/0.99  --smt_ac_axioms                         fast
% 1.55/0.99  --preprocessed_out                      false
% 1.55/0.99  --preprocessed_stats                    false
% 1.55/0.99  
% 1.55/0.99  ------ Abstraction refinement Options
% 1.55/0.99  
% 1.55/0.99  --abstr_ref                             []
% 1.55/0.99  --abstr_ref_prep                        false
% 1.55/0.99  --abstr_ref_until_sat                   false
% 1.55/0.99  --abstr_ref_sig_restrict                funpre
% 1.55/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.55/0.99  --abstr_ref_under                       []
% 1.55/0.99  
% 1.55/0.99  ------ SAT Options
% 1.55/0.99  
% 1.55/0.99  --sat_mode                              false
% 1.55/0.99  --sat_fm_restart_options                ""
% 1.55/0.99  --sat_gr_def                            false
% 1.55/0.99  --sat_epr_types                         true
% 1.55/0.99  --sat_non_cyclic_types                  false
% 1.55/0.99  --sat_finite_models                     false
% 1.55/0.99  --sat_fm_lemmas                         false
% 1.55/0.99  --sat_fm_prep                           false
% 1.55/0.99  --sat_fm_uc_incr                        true
% 1.55/0.99  --sat_out_model                         small
% 1.55/0.99  --sat_out_clauses                       false
% 1.55/0.99  
% 1.55/0.99  ------ QBF Options
% 1.55/0.99  
% 1.55/0.99  --qbf_mode                              false
% 1.55/0.99  --qbf_elim_univ                         false
% 1.55/0.99  --qbf_dom_inst                          none
% 1.55/0.99  --qbf_dom_pre_inst                      false
% 1.55/0.99  --qbf_sk_in                             false
% 1.55/0.99  --qbf_pred_elim                         true
% 1.55/0.99  --qbf_split                             512
% 1.55/0.99  
% 1.55/0.99  ------ BMC1 Options
% 1.55/0.99  
% 1.55/0.99  --bmc1_incremental                      false
% 1.55/0.99  --bmc1_axioms                           reachable_all
% 1.55/0.99  --bmc1_min_bound                        0
% 1.55/0.99  --bmc1_max_bound                        -1
% 1.55/0.99  --bmc1_max_bound_default                -1
% 1.55/0.99  --bmc1_symbol_reachability              true
% 1.55/0.99  --bmc1_property_lemmas                  false
% 1.55/0.99  --bmc1_k_induction                      false
% 1.55/0.99  --bmc1_non_equiv_states                 false
% 1.55/0.99  --bmc1_deadlock                         false
% 1.55/0.99  --bmc1_ucm                              false
% 1.55/0.99  --bmc1_add_unsat_core                   none
% 1.55/0.99  --bmc1_unsat_core_children              false
% 1.55/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.55/0.99  --bmc1_out_stat                         full
% 1.55/0.99  --bmc1_ground_init                      false
% 1.55/0.99  --bmc1_pre_inst_next_state              false
% 1.55/0.99  --bmc1_pre_inst_state                   false
% 1.55/0.99  --bmc1_pre_inst_reach_state             false
% 1.55/0.99  --bmc1_out_unsat_core                   false
% 1.55/0.99  --bmc1_aig_witness_out                  false
% 1.55/0.99  --bmc1_verbose                          false
% 1.55/0.99  --bmc1_dump_clauses_tptp                false
% 1.55/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.55/0.99  --bmc1_dump_file                        -
% 1.55/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.55/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.55/0.99  --bmc1_ucm_extend_mode                  1
% 1.55/0.99  --bmc1_ucm_init_mode                    2
% 1.55/0.99  --bmc1_ucm_cone_mode                    none
% 1.55/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.55/0.99  --bmc1_ucm_relax_model                  4
% 1.55/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.55/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.55/0.99  --bmc1_ucm_layered_model                none
% 1.55/0.99  --bmc1_ucm_max_lemma_size               10
% 1.55/0.99  
% 1.55/0.99  ------ AIG Options
% 1.55/0.99  
% 1.55/0.99  --aig_mode                              false
% 1.55/0.99  
% 1.55/0.99  ------ Instantiation Options
% 1.55/0.99  
% 1.55/0.99  --instantiation_flag                    true
% 1.55/0.99  --inst_sos_flag                         false
% 1.55/0.99  --inst_sos_phase                        true
% 1.55/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.55/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.55/0.99  --inst_lit_sel_side                     none
% 1.55/0.99  --inst_solver_per_active                1400
% 1.55/0.99  --inst_solver_calls_frac                1.
% 1.55/0.99  --inst_passive_queue_type               priority_queues
% 1.55/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.55/0.99  --inst_passive_queues_freq              [25;2]
% 1.55/0.99  --inst_dismatching                      true
% 1.55/0.99  --inst_eager_unprocessed_to_passive     true
% 1.55/0.99  --inst_prop_sim_given                   true
% 1.55/0.99  --inst_prop_sim_new                     false
% 1.55/0.99  --inst_subs_new                         false
% 1.55/0.99  --inst_eq_res_simp                      false
% 1.55/0.99  --inst_subs_given                       false
% 1.55/0.99  --inst_orphan_elimination               true
% 1.55/0.99  --inst_learning_loop_flag               true
% 1.55/0.99  --inst_learning_start                   3000
% 1.55/0.99  --inst_learning_factor                  2
% 1.55/0.99  --inst_start_prop_sim_after_learn       3
% 1.55/0.99  --inst_sel_renew                        solver
% 1.55/0.99  --inst_lit_activity_flag                true
% 1.55/0.99  --inst_restr_to_given                   false
% 1.55/0.99  --inst_activity_threshold               500
% 1.55/0.99  --inst_out_proof                        true
% 1.55/0.99  
% 1.55/0.99  ------ Resolution Options
% 1.55/0.99  
% 1.55/0.99  --resolution_flag                       false
% 1.55/0.99  --res_lit_sel                           adaptive
% 1.55/0.99  --res_lit_sel_side                      none
% 1.55/0.99  --res_ordering                          kbo
% 1.55/0.99  --res_to_prop_solver                    active
% 1.55/0.99  --res_prop_simpl_new                    false
% 1.55/0.99  --res_prop_simpl_given                  true
% 1.55/0.99  --res_passive_queue_type                priority_queues
% 1.55/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.55/0.99  --res_passive_queues_freq               [15;5]
% 1.55/0.99  --res_forward_subs                      full
% 1.55/0.99  --res_backward_subs                     full
% 1.55/0.99  --res_forward_subs_resolution           true
% 1.55/0.99  --res_backward_subs_resolution          true
% 1.55/0.99  --res_orphan_elimination                true
% 1.55/0.99  --res_time_limit                        2.
% 1.55/0.99  --res_out_proof                         true
% 1.55/0.99  
% 1.55/0.99  ------ Superposition Options
% 1.55/0.99  
% 1.55/0.99  --superposition_flag                    true
% 1.55/0.99  --sup_passive_queue_type                priority_queues
% 1.55/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.55/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.55/0.99  --demod_completeness_check              fast
% 1.55/0.99  --demod_use_ground                      true
% 1.55/0.99  --sup_to_prop_solver                    passive
% 1.55/0.99  --sup_prop_simpl_new                    true
% 1.55/0.99  --sup_prop_simpl_given                  true
% 1.55/0.99  --sup_fun_splitting                     false
% 1.55/0.99  --sup_smt_interval                      50000
% 1.55/0.99  
% 1.55/0.99  ------ Superposition Simplification Setup
% 1.55/0.99  
% 1.55/0.99  --sup_indices_passive                   []
% 1.55/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.55/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/0.99  --sup_full_bw                           [BwDemod]
% 1.55/0.99  --sup_immed_triv                        [TrivRules]
% 1.55/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.55/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/0.99  --sup_immed_bw_main                     []
% 1.55/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.55/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/0.99  
% 1.55/0.99  ------ Combination Options
% 1.55/0.99  
% 1.55/0.99  --comb_res_mult                         3
% 1.55/0.99  --comb_sup_mult                         2
% 1.55/0.99  --comb_inst_mult                        10
% 1.55/0.99  
% 1.55/0.99  ------ Debug Options
% 1.55/0.99  
% 1.55/0.99  --dbg_backtrace                         false
% 1.55/0.99  --dbg_dump_prop_clauses                 false
% 1.55/0.99  --dbg_dump_prop_clauses_file            -
% 1.55/0.99  --dbg_out_stat                          false
% 1.55/0.99  
% 1.55/0.99  
% 1.55/0.99  
% 1.55/0.99  
% 1.55/0.99  ------ Proving...
% 1.55/0.99  
% 1.55/0.99  
% 1.55/0.99  % SZS status Theorem for theBenchmark.p
% 1.55/0.99  
% 1.55/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.55/0.99  
% 1.55/0.99  fof(f8,conjecture,(
% 1.55/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 1.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/0.99  
% 1.55/0.99  fof(f9,negated_conjecture,(
% 1.55/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 1.55/0.99    inference(negated_conjecture,[],[f8])).
% 1.55/0.99  
% 1.55/0.99  fof(f18,plain,(
% 1.55/0.99    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 1.55/0.99    inference(ennf_transformation,[],[f9])).
% 1.55/0.99  
% 1.55/0.99  fof(f31,plain,(
% 1.55/0.99    ( ! [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) => (~r1_tarski(sK4,sK6) & (r1_tarski(k2_zfmisc_1(sK4,X0),k2_zfmisc_1(sK6,sK5)) | r1_tarski(k2_zfmisc_1(X0,sK4),k2_zfmisc_1(sK5,sK6))))) )),
% 1.55/0.99    introduced(choice_axiom,[])).
% 1.55/0.99  
% 1.55/0.99  fof(f30,plain,(
% 1.55/0.99    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0)) => (? [X3,X2,X1] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(sK3,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(sK3))),
% 1.55/0.99    introduced(choice_axiom,[])).
% 1.55/0.99  
% 1.55/0.99  fof(f32,plain,(
% 1.55/0.99    (~r1_tarski(sK4,sK6) & (r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6)))) & ~v1_xboole_0(sK3)),
% 1.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f18,f31,f30])).
% 1.55/0.99  
% 1.55/0.99  fof(f48,plain,(
% 1.55/0.99    r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6))),
% 1.55/0.99    inference(cnf_transformation,[],[f32])).
% 1.55/0.99  
% 1.55/0.99  fof(f2,axiom,(
% 1.55/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/0.99  
% 1.55/0.99  fof(f14,plain,(
% 1.55/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.55/0.99    inference(ennf_transformation,[],[f2])).
% 1.55/0.99  
% 1.55/0.99  fof(f21,plain,(
% 1.55/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.99    inference(nnf_transformation,[],[f14])).
% 1.55/0.99  
% 1.55/0.99  fof(f22,plain,(
% 1.55/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.99    inference(rectify,[],[f21])).
% 1.55/0.99  
% 1.55/0.99  fof(f23,plain,(
% 1.55/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.55/0.99    introduced(choice_axiom,[])).
% 1.55/0.99  
% 1.55/0.99  fof(f24,plain,(
% 1.55/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 1.55/0.99  
% 1.55/0.99  fof(f34,plain,(
% 1.55/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.55/0.99    inference(cnf_transformation,[],[f24])).
% 1.55/0.99  
% 1.55/0.99  fof(f7,axiom,(
% 1.55/0.99    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/0.99  
% 1.55/0.99  fof(f16,plain,(
% 1.55/0.99    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.55/0.99    inference(ennf_transformation,[],[f7])).
% 1.55/0.99  
% 1.55/0.99  fof(f17,plain,(
% 1.55/0.99    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.55/0.99    inference(flattening,[],[f16])).
% 1.55/0.99  
% 1.55/0.99  fof(f45,plain,(
% 1.55/0.99    ( ! [X2,X0,X3,X1] : (r1_tarski(X0,X2) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.55/0.99    inference(cnf_transformation,[],[f17])).
% 1.55/0.99  
% 1.55/0.99  fof(f49,plain,(
% 1.55/0.99    ~r1_tarski(sK4,sK6)),
% 1.55/0.99    inference(cnf_transformation,[],[f32])).
% 1.55/0.99  
% 1.55/0.99  fof(f4,axiom,(
% 1.55/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/0.99  
% 1.55/0.99  fof(f10,plain,(
% 1.55/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.55/0.99    inference(rectify,[],[f4])).
% 1.55/0.99  
% 1.55/0.99  fof(f39,plain,(
% 1.55/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.55/0.99    inference(cnf_transformation,[],[f10])).
% 1.55/0.99  
% 1.55/0.99  fof(f3,axiom,(
% 1.55/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/0.99  
% 1.55/0.99  fof(f25,plain,(
% 1.55/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.55/0.99    inference(nnf_transformation,[],[f3])).
% 1.55/0.99  
% 1.55/0.99  fof(f38,plain,(
% 1.55/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.55/0.99    inference(cnf_transformation,[],[f25])).
% 1.55/0.99  
% 1.55/0.99  fof(f1,axiom,(
% 1.55/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/0.99  
% 1.55/0.99  fof(f12,plain,(
% 1.55/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.55/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 1.55/0.99  
% 1.55/0.99  fof(f13,plain,(
% 1.55/0.99    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.55/0.99    inference(ennf_transformation,[],[f12])).
% 1.55/0.99  
% 1.55/0.99  fof(f19,plain,(
% 1.55/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.55/0.99    introduced(choice_axiom,[])).
% 1.55/0.99  
% 1.55/0.99  fof(f20,plain,(
% 1.55/0.99    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 1.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f19])).
% 1.55/0.99  
% 1.55/0.99  fof(f33,plain,(
% 1.55/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.55/0.99    inference(cnf_transformation,[],[f20])).
% 1.55/0.99  
% 1.55/0.99  fof(f47,plain,(
% 1.55/0.99    ~v1_xboole_0(sK3)),
% 1.55/0.99    inference(cnf_transformation,[],[f32])).
% 1.55/0.99  
% 1.55/0.99  fof(f35,plain,(
% 1.55/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.55/0.99    inference(cnf_transformation,[],[f24])).
% 1.55/0.99  
% 1.55/0.99  fof(f5,axiom,(
% 1.55/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/0.99  
% 1.55/0.99  fof(f11,plain,(
% 1.55/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.55/0.99    inference(rectify,[],[f5])).
% 1.55/0.99  
% 1.55/0.99  fof(f15,plain,(
% 1.55/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.55/0.99    inference(ennf_transformation,[],[f11])).
% 1.55/0.99  
% 1.55/0.99  fof(f26,plain,(
% 1.55/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.55/0.99    introduced(choice_axiom,[])).
% 1.55/0.99  
% 1.55/0.99  fof(f27,plain,(
% 1.55/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.55/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f26])).
% 1.55/0.99  
% 1.55/0.99  fof(f41,plain,(
% 1.55/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.55/0.99    inference(cnf_transformation,[],[f27])).
% 1.55/0.99  
% 1.55/0.99  fof(f36,plain,(
% 1.55/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 1.55/0.99    inference(cnf_transformation,[],[f24])).
% 1.55/0.99  
% 1.55/0.99  fof(f46,plain,(
% 1.55/0.99    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.55/0.99    inference(cnf_transformation,[],[f17])).
% 1.55/0.99  
% 1.55/0.99  fof(f6,axiom,(
% 1.55/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.55/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/0.99  
% 1.55/0.99  fof(f28,plain,(
% 1.55/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.55/0.99    inference(nnf_transformation,[],[f6])).
% 1.55/0.99  
% 1.55/0.99  fof(f29,plain,(
% 1.55/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.55/0.99    inference(flattening,[],[f28])).
% 1.55/0.99  
% 1.55/0.99  fof(f42,plain,(
% 1.55/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 1.55/0.99    inference(cnf_transformation,[],[f29])).
% 1.55/0.99  
% 1.55/0.99  cnf(c_15,negated_conjecture,
% 1.55/0.99      ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6))
% 1.55/0.99      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) ),
% 1.55/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_697,plain,
% 1.55/0.99      ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6)) = iProver_top
% 1.55/0.99      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top ),
% 1.55/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_3,plain,
% 1.55/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 1.55/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_705,plain,
% 1.55/0.99      ( r1_tarski(X0,X1) != iProver_top
% 1.55/0.99      | r2_hidden(X2,X0) != iProver_top
% 1.55/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 1.55/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1665,plain,
% 1.55/0.99      ( r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top
% 1.55/0.99      | r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
% 1.55/0.99      | r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 1.55/0.99      inference(superposition,[status(thm)],[c_697,c_705]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_13,plain,
% 1.55/0.99      ( r1_tarski(X0,X1)
% 1.55/0.99      | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
% 1.55/0.99      | k2_zfmisc_1(X0,X2) = k1_xboole_0 ),
% 1.55/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_699,plain,
% 1.55/0.99      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 1.55/0.99      | r1_tarski(X0,X2) = iProver_top
% 1.55/0.99      | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) != iProver_top ),
% 1.55/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1869,plain,
% 1.55/0.99      ( k2_zfmisc_1(sK4,sK3) = k1_xboole_0
% 1.55/0.99      | r1_tarski(sK4,sK6) = iProver_top
% 1.55/0.99      | r2_hidden(X0,k2_zfmisc_1(sK5,sK6)) = iProver_top
% 1.55/0.99      | r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 1.55/0.99      inference(superposition,[status(thm)],[c_1665,c_699]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_14,negated_conjecture,
% 1.55/0.99      ( ~ r1_tarski(sK4,sK6) ),
% 1.55/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_6,plain,
% 1.55/0.99      ( k3_xboole_0(X0,X0) = X0 ),
% 1.55/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_32,plain,
% 1.55/0.99      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_4,plain,
% 1.55/0.99      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 1.55/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_35,plain,
% 1.55/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.55/0.99      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_0,plain,
% 1.55/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.55/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_16,negated_conjecture,
% 1.55/0.99      ( ~ v1_xboole_0(sK3) ),
% 1.55/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_187,plain,
% 1.55/0.99      ( r2_hidden(sK0(X0),X0) | sK3 != X0 ),
% 1.55/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_188,plain,
% 1.55/0.99      ( r2_hidden(sK0(sK3),sK3) ),
% 1.55/0.99      inference(unflattening,[status(thm)],[c_187]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_2,plain,
% 1.55/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 1.55/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_799,plain,
% 1.55/0.99      ( r1_tarski(sK4,sK6) | r2_hidden(sK1(sK4,sK6),sK4) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_802,plain,
% 1.55/0.99      ( ~ r1_tarski(sK3,X0)
% 1.55/0.99      | r2_hidden(sK0(sK3),X0)
% 1.55/0.99      | ~ r2_hidden(sK0(sK3),sK3) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1058,plain,
% 1.55/0.99      ( ~ r1_tarski(sK3,k3_xboole_0(X0,X1))
% 1.55/0.99      | r2_hidden(sK0(sK3),k3_xboole_0(X0,X1))
% 1.55/0.99      | ~ r2_hidden(sK0(sK3),sK3) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_802]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1061,plain,
% 1.55/0.99      ( ~ r1_tarski(sK3,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 1.55/0.99      | r2_hidden(sK0(sK3),k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 1.55/0.99      | ~ r2_hidden(sK0(sK3),sK3) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_1058]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_7,plain,
% 1.55/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 1.55/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1059,plain,
% 1.55/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(sK0(sK3),k3_xboole_0(X0,X1)) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1065,plain,
% 1.55/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.55/0.99      | ~ r2_hidden(sK0(sK3),k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_1059]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_706,plain,
% 1.55/0.99      ( r1_tarski(X0,X1) = iProver_top
% 1.55/0.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 1.55/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1,plain,
% 1.55/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 1.55/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_707,plain,
% 1.55/0.99      ( r1_tarski(X0,X1) = iProver_top
% 1.55/0.99      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 1.55/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1102,plain,
% 1.55/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 1.55/0.99      inference(superposition,[status(thm)],[c_706,c_707]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1103,plain,
% 1.55/0.99      ( r1_tarski(X0,X0) ),
% 1.55/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1102]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1105,plain,
% 1.55/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_1103]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_835,plain,
% 1.55/0.99      ( ~ r1_tarski(sK4,X0)
% 1.55/0.99      | r2_hidden(sK1(sK4,sK6),X0)
% 1.55/0.99      | ~ r2_hidden(sK1(sK4,sK6),sK4) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1111,plain,
% 1.55/0.99      ( ~ r1_tarski(sK4,k3_xboole_0(X0,X1))
% 1.55/0.99      | r2_hidden(sK1(sK4,sK6),k3_xboole_0(X0,X1))
% 1.55/0.99      | ~ r2_hidden(sK1(sK4,sK6),sK4) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_835]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1114,plain,
% 1.55/0.99      ( ~ r1_tarski(sK4,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 1.55/0.99      | r2_hidden(sK1(sK4,sK6),k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 1.55/0.99      | ~ r2_hidden(sK1(sK4,sK6),sK4) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_1111]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1112,plain,
% 1.55/0.99      ( ~ r1_xboole_0(X0,X1)
% 1.55/0.99      | ~ r2_hidden(sK1(sK4,sK6),k3_xboole_0(X0,X1)) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1118,plain,
% 1.55/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.55/0.99      | ~ r2_hidden(sK1(sK4,sK6),k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_1112]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_391,plain,
% 1.55/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.55/0.99      theory(equality) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_925,plain,
% 1.55/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_391]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1356,plain,
% 1.55/0.99      ( ~ r1_tarski(X0,X1)
% 1.55/0.99      | r1_tarski(sK3,k3_xboole_0(X2,X3))
% 1.55/0.99      | k3_xboole_0(X2,X3) != X1
% 1.55/0.99      | sK3 != X0 ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_925]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1363,plain,
% 1.55/0.99      ( r1_tarski(sK3,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 1.55/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 1.55/0.99      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.55/0.99      | sK3 != k1_xboole_0 ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_1356]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_972,plain,
% 1.55/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X2) | X2 != X1 | sK4 != X0 ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_391]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1434,plain,
% 1.55/0.99      ( ~ r1_tarski(X0,X1)
% 1.55/0.99      | r1_tarski(sK4,k3_xboole_0(X2,X3))
% 1.55/0.99      | k3_xboole_0(X2,X3) != X1
% 1.55/0.99      | sK4 != X0 ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_972]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1436,plain,
% 1.55/0.99      ( r1_tarski(sK4,k3_xboole_0(k1_xboole_0,k1_xboole_0))
% 1.55/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 1.55/0.99      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.55/0.99      | sK4 != k1_xboole_0 ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_1434]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1568,plain,
% 1.55/0.99      ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
% 1.55/0.99      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top
% 1.55/0.99      | r1_tarski(sK3,sK5) = iProver_top ),
% 1.55/0.99      inference(superposition,[status(thm)],[c_697,c_699]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_18,plain,
% 1.55/0.99      ( r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6)) = iProver_top
% 1.55/0.99      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top ),
% 1.55/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_19,plain,
% 1.55/0.99      ( r1_tarski(sK4,sK6) != iProver_top ),
% 1.55/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_12,plain,
% 1.55/0.99      ( r1_tarski(X0,X1)
% 1.55/0.99      | ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))
% 1.55/0.99      | k2_zfmisc_1(X2,X0) = k1_xboole_0 ),
% 1.55/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_807,plain,
% 1.55/0.99      ( ~ r1_tarski(k2_zfmisc_1(X0,sK4),k2_zfmisc_1(X1,sK6))
% 1.55/0.99      | r1_tarski(sK4,sK6)
% 1.55/0.99      | k2_zfmisc_1(X0,sK4) = k1_xboole_0 ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_865,plain,
% 1.55/0.99      ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6))
% 1.55/0.99      | r1_tarski(sK4,sK6)
% 1.55/0.99      | k2_zfmisc_1(sK3,sK4) = k1_xboole_0 ),
% 1.55/0.99      inference(instantiation,[status(thm)],[c_807]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_866,plain,
% 1.55/0.99      ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
% 1.55/0.99      | r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(sK5,sK6)) != iProver_top
% 1.55/0.99      | r1_tarski(sK4,sK6) = iProver_top ),
% 1.55/0.99      inference(predicate_to_equality,[status(thm)],[c_865]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1746,plain,
% 1.55/0.99      ( r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top
% 1.55/0.99      | k2_zfmisc_1(sK3,sK4) = k1_xboole_0 ),
% 1.55/0.99      inference(global_propositional_subsumption,
% 1.55/0.99                [status(thm)],
% 1.55/0.99                [c_1568,c_18,c_19,c_866]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1747,plain,
% 1.55/0.99      ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
% 1.55/0.99      | r1_tarski(k2_zfmisc_1(sK4,sK3),k2_zfmisc_1(sK6,sK5)) = iProver_top ),
% 1.55/0.99      inference(renaming,[status(thm)],[c_1746]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1753,plain,
% 1.55/0.99      ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
% 1.55/0.99      | k2_zfmisc_1(sK4,sK3) = k1_xboole_0
% 1.55/0.99      | r1_tarski(sK4,sK6) = iProver_top ),
% 1.55/0.99      inference(superposition,[status(thm)],[c_1747,c_699]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1769,plain,
% 1.55/0.99      ( r1_tarski(sK4,sK6)
% 1.55/0.99      | k2_zfmisc_1(sK3,sK4) = k1_xboole_0
% 1.55/0.99      | k2_zfmisc_1(sK4,sK3) = k1_xboole_0 ),
% 1.55/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1753]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1902,plain,
% 1.55/0.99      ( k2_zfmisc_1(sK4,sK3) = k1_xboole_0
% 1.55/0.99      | k2_zfmisc_1(sK3,sK4) = k1_xboole_0 ),
% 1.55/0.99      inference(global_propositional_subsumption,
% 1.55/0.99                [status(thm)],
% 1.55/0.99                [c_1753,c_14,c_1769]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1903,plain,
% 1.55/0.99      ( k2_zfmisc_1(sK3,sK4) = k1_xboole_0
% 1.55/0.99      | k2_zfmisc_1(sK4,sK3) = k1_xboole_0 ),
% 1.55/0.99      inference(renaming,[status(thm)],[c_1902]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_11,plain,
% 1.55/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 1.55/0.99      | k1_xboole_0 = X1
% 1.55/0.99      | k1_xboole_0 = X0 ),
% 1.55/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_1908,plain,
% 1.55/0.99      ( k2_zfmisc_1(sK4,sK3) = k1_xboole_0
% 1.55/0.99      | sK3 = k1_xboole_0
% 1.55/0.99      | sK4 = k1_xboole_0 ),
% 1.55/0.99      inference(superposition,[status(thm)],[c_1903,c_11]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_2039,plain,
% 1.55/0.99      ( k2_zfmisc_1(sK4,sK3) = k1_xboole_0 ),
% 1.55/0.99      inference(global_propositional_subsumption,
% 1.55/0.99                [status(thm)],
% 1.55/0.99                [c_1869,c_14,c_32,c_35,c_188,c_799,c_1061,c_1065,c_1105,
% 1.55/0.99                 c_1114,c_1118,c_1363,c_1436,c_1908]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(c_2055,plain,
% 1.55/0.99      ( sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 1.55/0.99      inference(superposition,[status(thm)],[c_2039,c_11]) ).
% 1.55/0.99  
% 1.55/0.99  cnf(contradiction,plain,
% 1.55/0.99      ( $false ),
% 1.55/0.99      inference(minisat,
% 1.55/0.99                [status(thm)],
% 1.55/0.99                [c_2055,c_1436,c_1363,c_1118,c_1114,c_1105,c_1065,c_1061,
% 1.55/0.99                 c_799,c_188,c_35,c_32,c_14]) ).
% 1.55/0.99  
% 1.55/0.99  
% 1.55/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.55/0.99  
% 1.55/0.99  ------                               Statistics
% 1.55/0.99  
% 1.55/0.99  ------ General
% 1.55/0.99  
% 1.55/0.99  abstr_ref_over_cycles:                  0
% 1.55/0.99  abstr_ref_under_cycles:                 0
% 1.55/0.99  gc_basic_clause_elim:                   0
% 1.55/0.99  forced_gc_time:                         0
% 1.55/0.99  parsing_time:                           0.011
% 1.55/0.99  unif_index_cands_time:                  0.
% 1.55/0.99  unif_index_add_time:                    0.
% 1.55/0.99  orderings_time:                         0.
% 1.55/0.99  out_proof_time:                         0.008
% 1.55/0.99  total_time:                             0.089
% 1.55/0.99  num_of_symbols:                         45
% 1.55/0.99  num_of_terms:                           1732
% 1.55/0.99  
% 1.55/0.99  ------ Preprocessing
% 1.55/0.99  
% 1.55/0.99  num_of_splits:                          0
% 1.55/0.99  num_of_split_atoms:                     0
% 1.55/0.99  num_of_reused_defs:                     0
% 1.55/0.99  num_eq_ax_congr_red:                    25
% 1.55/0.99  num_of_sem_filtered_clauses:            1
% 1.55/0.99  num_of_subtypes:                        0
% 1.55/0.99  monotx_restored_types:                  0
% 1.55/0.99  sat_num_of_epr_types:                   0
% 1.55/0.99  sat_num_of_non_cyclic_types:            0
% 1.55/0.99  sat_guarded_non_collapsed_types:        0
% 1.55/0.99  num_pure_diseq_elim:                    0
% 1.55/0.99  simp_replaced_by:                       0
% 1.55/0.99  res_preprocessed:                       78
% 1.55/0.99  prep_upred:                             0
% 1.55/0.99  prep_unflattend:                        1
% 1.55/0.99  smt_new_axioms:                         0
% 1.55/0.99  pred_elim_cands:                        3
% 1.55/0.99  pred_elim:                              1
% 1.55/0.99  pred_elim_cl:                           1
% 1.55/0.99  pred_elim_cycles:                       3
% 1.55/0.99  merged_defs:                            8
% 1.55/0.99  merged_defs_ncl:                        0
% 1.55/0.99  bin_hyper_res:                          8
% 1.55/0.99  prep_cycles:                            4
% 1.55/0.99  pred_elim_time:                         0.001
% 1.55/0.99  splitting_time:                         0.
% 1.55/0.99  sem_filter_time:                        0.
% 1.55/0.99  monotx_time:                            0.
% 1.55/0.99  subtype_inf_time:                       0.
% 1.55/0.99  
% 1.55/0.99  ------ Problem properties
% 1.55/0.99  
% 1.55/0.99  clauses:                                16
% 1.55/0.99  conjectures:                            2
% 1.55/0.99  epr:                                    2
% 1.55/0.99  horn:                                   10
% 1.55/0.99  ground:                                 3
% 1.55/0.99  unary:                                  5
% 1.55/0.99  binary:                                 7
% 1.55/0.99  lits:                                   31
% 1.55/0.99  lits_eq:                                10
% 1.55/0.99  fd_pure:                                0
% 1.55/0.99  fd_pseudo:                              0
% 1.55/0.99  fd_cond:                                1
% 1.55/0.99  fd_pseudo_cond:                         0
% 1.55/0.99  ac_symbols:                             0
% 1.55/0.99  
% 1.55/0.99  ------ Propositional Solver
% 1.55/0.99  
% 1.55/0.99  prop_solver_calls:                      28
% 1.55/0.99  prop_fast_solver_calls:                 401
% 1.55/0.99  smt_solver_calls:                       0
% 1.55/0.99  smt_fast_solver_calls:                  0
% 1.55/0.99  prop_num_of_clauses:                    646
% 1.55/0.99  prop_preprocess_simplified:             2877
% 1.55/0.99  prop_fo_subsumed:                       5
% 1.55/0.99  prop_solver_time:                       0.
% 1.55/0.99  smt_solver_time:                        0.
% 1.55/0.99  smt_fast_solver_time:                   0.
% 1.55/0.99  prop_fast_solver_time:                  0.
% 1.55/0.99  prop_unsat_core_time:                   0.
% 1.55/0.99  
% 1.55/0.99  ------ QBF
% 1.55/0.99  
% 1.55/0.99  qbf_q_res:                              0
% 1.55/0.99  qbf_num_tautologies:                    0
% 1.55/0.99  qbf_prep_cycles:                        0
% 1.55/0.99  
% 1.55/0.99  ------ BMC1
% 1.55/0.99  
% 1.55/0.99  bmc1_current_bound:                     -1
% 1.55/0.99  bmc1_last_solved_bound:                 -1
% 1.55/0.99  bmc1_unsat_core_size:                   -1
% 1.55/0.99  bmc1_unsat_core_parents_size:           -1
% 1.55/0.99  bmc1_merge_next_fun:                    0
% 1.55/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.55/0.99  
% 1.55/0.99  ------ Instantiation
% 1.55/0.99  
% 1.55/0.99  inst_num_of_clauses:                    217
% 1.55/0.99  inst_num_in_passive:                    81
% 1.55/0.99  inst_num_in_active:                     128
% 1.55/0.99  inst_num_in_unprocessed:                8
% 1.55/0.99  inst_num_of_loops:                      150
% 1.55/0.99  inst_num_of_learning_restarts:          0
% 1.55/0.99  inst_num_moves_active_passive:          19
% 1.55/0.99  inst_lit_activity:                      0
% 1.55/0.99  inst_lit_activity_moves:                0
% 1.55/0.99  inst_num_tautologies:                   0
% 1.55/0.99  inst_num_prop_implied:                  0
% 1.55/0.99  inst_num_existing_simplified:           0
% 1.55/0.99  inst_num_eq_res_simplified:             0
% 1.55/0.99  inst_num_child_elim:                    0
% 1.55/0.99  inst_num_of_dismatching_blockings:      39
% 1.55/0.99  inst_num_of_non_proper_insts:           176
% 1.55/0.99  inst_num_of_duplicates:                 0
% 1.55/0.99  inst_inst_num_from_inst_to_res:         0
% 1.55/0.99  inst_dismatching_checking_time:         0.
% 1.55/0.99  
% 1.55/0.99  ------ Resolution
% 1.55/0.99  
% 1.55/0.99  res_num_of_clauses:                     0
% 1.55/0.99  res_num_in_passive:                     0
% 1.55/0.99  res_num_in_active:                      0
% 1.55/0.99  res_num_of_loops:                       82
% 1.55/0.99  res_forward_subset_subsumed:            12
% 1.55/0.99  res_backward_subset_subsumed:           0
% 1.55/0.99  res_forward_subsumed:                   0
% 1.55/0.99  res_backward_subsumed:                  0
% 1.55/0.99  res_forward_subsumption_resolution:     0
% 1.55/0.99  res_backward_subsumption_resolution:    0
% 1.55/0.99  res_clause_to_clause_subsumption:       112
% 1.55/0.99  res_orphan_elimination:                 0
% 1.55/0.99  res_tautology_del:                      30
% 1.55/0.99  res_num_eq_res_simplified:              0
% 1.55/0.99  res_num_sel_changes:                    0
% 1.55/0.99  res_moves_from_active_to_pass:          0
% 1.55/0.99  
% 1.55/0.99  ------ Superposition
% 1.55/0.99  
% 1.55/0.99  sup_time_total:                         0.
% 1.55/0.99  sup_time_generating:                    0.
% 1.55/0.99  sup_time_sim_full:                      0.
% 1.55/0.99  sup_time_sim_immed:                     0.
% 1.55/0.99  
% 1.55/0.99  sup_num_of_clauses:                     34
% 1.55/0.99  sup_num_in_active:                      26
% 1.55/0.99  sup_num_in_passive:                     8
% 1.55/0.99  sup_num_of_loops:                       29
% 1.55/0.99  sup_fw_superposition:                   25
% 1.55/0.99  sup_bw_superposition:                   18
% 1.55/0.99  sup_immediate_simplified:               19
% 1.55/0.99  sup_given_eliminated:                   0
% 1.55/0.99  comparisons_done:                       0
% 1.55/0.99  comparisons_avoided:                    0
% 1.55/0.99  
% 1.55/0.99  ------ Simplifications
% 1.55/0.99  
% 1.55/0.99  
% 1.55/0.99  sim_fw_subset_subsumed:                 11
% 1.55/0.99  sim_bw_subset_subsumed:                 1
% 1.55/0.99  sim_fw_subsumed:                        8
% 1.55/0.99  sim_bw_subsumed:                        1
% 1.55/0.99  sim_fw_subsumption_res:                 0
% 1.55/0.99  sim_bw_subsumption_res:                 0
% 1.55/0.99  sim_tautology_del:                      2
% 1.55/0.99  sim_eq_tautology_del:                   1
% 1.55/0.99  sim_eq_res_simp:                        0
% 1.55/0.99  sim_fw_demodulated:                     0
% 1.55/0.99  sim_bw_demodulated:                     4
% 1.55/0.99  sim_light_normalised:                   0
% 1.55/0.99  sim_joinable_taut:                      0
% 1.55/0.99  sim_joinable_simp:                      0
% 1.55/0.99  sim_ac_normalised:                      0
% 1.55/0.99  sim_smt_subsumption:                    0
% 1.55/0.99  
%------------------------------------------------------------------------------
