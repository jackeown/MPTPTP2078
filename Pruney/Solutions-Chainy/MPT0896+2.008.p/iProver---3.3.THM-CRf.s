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
% DateTime   : Thu Dec  3 11:58:40 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 567 expanded)
%              Number of clauses        :   44 ( 102 expanded)
%              Number of leaves         :    7 ( 145 expanded)
%              Depth                    :   18
%              Number of atoms          :  284 (2918 expanded)
%              Number of equality atoms :  283 (2917 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f21])).

fof(f43,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f65,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f43,f49,f49])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f12])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f32,f26,f26,f26])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f33,f26,f26,f26])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f34,f26,f26,f26])).

fof(f48,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f17])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f66,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f72,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f63])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f68,plain,(
    ! [X2,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(equality_resolution,[],[f52])).

cnf(c_23,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_9,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1258,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(sK4,sK5) = X0 ),
    inference(superposition,[status(thm)],[c_23,c_9])).

cnf(c_1672,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1) ),
    inference(equality_resolution,[status(thm)],[c_1258])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_396,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),X2) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_541,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),sK2),X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_832,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),sK2),sK3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_1811,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_5419,plain,
    ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1672,c_22,c_21,c_20,c_19,c_1811])).

cnf(c_8,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_5460,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | sK5 = X1 ),
    inference(superposition,[status(thm)],[c_5419,c_8])).

cnf(c_5711,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) = k1_xboole_0
    | sK5 = sK1 ),
    inference(equality_resolution,[status(thm)],[c_5460])).

cnf(c_7,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_745,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK7 = X2 ),
    inference(superposition,[status(thm)],[c_23,c_7])).

cnf(c_921,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | sK7 = sK3 ),
    inference(equality_resolution,[status(thm)],[c_745])).

cnf(c_4415,plain,
    ( sK7 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_921,c_22,c_21,c_20,c_19,c_1811])).

cnf(c_18,negated_conjecture,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4438,plain,
    ( sK4 != sK0
    | sK5 != sK1
    | sK6 != sK2
    | sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_4415,c_18])).

cnf(c_4442,plain,
    ( sK4 != sK0
    | sK5 != sK1
    | sK6 != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_4438])).

cnf(c_1183,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK6 = X1 ),
    inference(superposition,[status(thm)],[c_23,c_8])).

cnf(c_1493,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | sK6 = sK2 ),
    inference(equality_resolution,[status(thm)],[c_1183])).

cnf(c_4678,plain,
    ( sK5 != sK1
    | sK4 != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4442,c_22,c_21,c_20,c_19,c_1493,c_1811])).

cnf(c_4679,plain,
    ( sK4 != sK0
    | sK5 != sK1 ),
    inference(renaming,[status(thm)],[c_4678])).

cnf(c_5469,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3)
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | sK4 = X0 ),
    inference(superposition,[status(thm)],[c_5419,c_9])).

cnf(c_5741,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) = k1_xboole_0
    | sK4 = sK0 ),
    inference(equality_resolution,[status(thm)],[c_5469])).

cnf(c_6837,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5711,c_4679,c_5741])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_752,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK7 = X2 ),
    inference(superposition,[status(thm)],[c_23,c_7])).

cnf(c_780,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | sK7 = X2 ),
    inference(demodulation,[status(thm)],[c_752,c_23])).

cnf(c_1037,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),X0) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | sK7 = X0 ),
    inference(superposition,[status(thm)],[c_23,c_780])).

cnf(c_2467,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),X0) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | sK7 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1037,c_22,c_21,c_20,c_19,c_1811])).

cnf(c_2472,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_2467])).

cnf(c_2584,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2472,c_22,c_21,c_20,c_19,c_1811])).

cnf(c_6853,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6837,c_2584])).

cnf(c_16,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_231,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_16,c_5])).

cnf(c_6870,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6853,c_231])).

cnf(c_6871,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6870])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:34:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.77/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/0.98  
% 2.77/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/0.98  
% 2.77/0.98  ------  iProver source info
% 2.77/0.98  
% 2.77/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.77/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/0.98  git: non_committed_changes: false
% 2.77/0.98  git: last_make_outside_of_git: false
% 2.77/0.98  
% 2.77/0.98  ------ 
% 2.77/0.98  
% 2.77/0.98  ------ Input Options
% 2.77/0.98  
% 2.77/0.98  --out_options                           all
% 2.77/0.98  --tptp_safe_out                         true
% 2.77/0.98  --problem_path                          ""
% 2.77/0.98  --include_path                          ""
% 2.77/0.98  --clausifier                            res/vclausify_rel
% 2.77/0.98  --clausifier_options                    --mode clausify
% 2.77/0.98  --stdin                                 false
% 2.77/0.98  --stats_out                             all
% 2.77/0.98  
% 2.77/0.98  ------ General Options
% 2.77/0.98  
% 2.77/0.98  --fof                                   false
% 2.77/0.98  --time_out_real                         305.
% 2.77/0.98  --time_out_virtual                      -1.
% 2.77/0.98  --symbol_type_check                     false
% 2.77/0.98  --clausify_out                          false
% 2.77/0.98  --sig_cnt_out                           false
% 2.77/0.98  --trig_cnt_out                          false
% 2.77/0.98  --trig_cnt_out_tolerance                1.
% 2.77/0.98  --trig_cnt_out_sk_spl                   false
% 2.77/0.98  --abstr_cl_out                          false
% 2.77/0.98  
% 2.77/0.98  ------ Global Options
% 2.77/0.98  
% 2.77/0.98  --schedule                              default
% 2.77/0.98  --add_important_lit                     false
% 2.77/0.98  --prop_solver_per_cl                    1000
% 2.77/0.98  --min_unsat_core                        false
% 2.77/0.98  --soft_assumptions                      false
% 2.77/0.98  --soft_lemma_size                       3
% 2.77/0.98  --prop_impl_unit_size                   0
% 2.77/0.98  --prop_impl_unit                        []
% 2.77/0.98  --share_sel_clauses                     true
% 2.77/0.98  --reset_solvers                         false
% 2.77/0.98  --bc_imp_inh                            [conj_cone]
% 2.77/0.98  --conj_cone_tolerance                   3.
% 2.77/0.98  --extra_neg_conj                        none
% 2.77/0.98  --large_theory_mode                     true
% 2.77/0.98  --prolific_symb_bound                   200
% 2.77/0.98  --lt_threshold                          2000
% 2.77/0.98  --clause_weak_htbl                      true
% 2.77/0.98  --gc_record_bc_elim                     false
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing Options
% 2.77/0.98  
% 2.77/0.98  --preprocessing_flag                    true
% 2.77/0.98  --time_out_prep_mult                    0.1
% 2.77/0.98  --splitting_mode                        input
% 2.77/0.98  --splitting_grd                         true
% 2.77/0.98  --splitting_cvd                         false
% 2.77/0.98  --splitting_cvd_svl                     false
% 2.77/0.98  --splitting_nvd                         32
% 2.77/0.98  --sub_typing                            true
% 2.77/0.98  --prep_gs_sim                           true
% 2.77/0.98  --prep_unflatten                        true
% 2.77/0.98  --prep_res_sim                          true
% 2.77/0.98  --prep_upred                            true
% 2.77/0.98  --prep_sem_filter                       exhaustive
% 2.77/0.98  --prep_sem_filter_out                   false
% 2.77/0.98  --pred_elim                             true
% 2.77/0.98  --res_sim_input                         true
% 2.77/0.98  --eq_ax_congr_red                       true
% 2.77/0.98  --pure_diseq_elim                       true
% 2.77/0.98  --brand_transform                       false
% 2.77/0.98  --non_eq_to_eq                          false
% 2.77/0.98  --prep_def_merge                        true
% 2.77/0.98  --prep_def_merge_prop_impl              false
% 2.77/0.98  --prep_def_merge_mbd                    true
% 2.77/0.98  --prep_def_merge_tr_red                 false
% 2.77/0.98  --prep_def_merge_tr_cl                  false
% 2.77/0.98  --smt_preprocessing                     true
% 2.77/0.98  --smt_ac_axioms                         fast
% 2.77/0.98  --preprocessed_out                      false
% 2.77/0.98  --preprocessed_stats                    false
% 2.77/0.98  
% 2.77/0.98  ------ Abstraction refinement Options
% 2.77/0.98  
% 2.77/0.98  --abstr_ref                             []
% 2.77/0.98  --abstr_ref_prep                        false
% 2.77/0.98  --abstr_ref_until_sat                   false
% 2.77/0.98  --abstr_ref_sig_restrict                funpre
% 2.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/0.98  --abstr_ref_under                       []
% 2.77/0.98  
% 2.77/0.98  ------ SAT Options
% 2.77/0.98  
% 2.77/0.98  --sat_mode                              false
% 2.77/0.98  --sat_fm_restart_options                ""
% 2.77/0.98  --sat_gr_def                            false
% 2.77/0.98  --sat_epr_types                         true
% 2.77/0.98  --sat_non_cyclic_types                  false
% 2.77/0.98  --sat_finite_models                     false
% 2.77/0.98  --sat_fm_lemmas                         false
% 2.77/0.98  --sat_fm_prep                           false
% 2.77/0.98  --sat_fm_uc_incr                        true
% 2.77/0.98  --sat_out_model                         small
% 2.77/0.98  --sat_out_clauses                       false
% 2.77/0.98  
% 2.77/0.98  ------ QBF Options
% 2.77/0.98  
% 2.77/0.98  --qbf_mode                              false
% 2.77/0.98  --qbf_elim_univ                         false
% 2.77/0.98  --qbf_dom_inst                          none
% 2.77/0.98  --qbf_dom_pre_inst                      false
% 2.77/0.98  --qbf_sk_in                             false
% 2.77/0.98  --qbf_pred_elim                         true
% 2.77/0.98  --qbf_split                             512
% 2.77/0.98  
% 2.77/0.98  ------ BMC1 Options
% 2.77/0.98  
% 2.77/0.98  --bmc1_incremental                      false
% 2.77/0.98  --bmc1_axioms                           reachable_all
% 2.77/0.98  --bmc1_min_bound                        0
% 2.77/0.98  --bmc1_max_bound                        -1
% 2.77/0.98  --bmc1_max_bound_default                -1
% 2.77/0.98  --bmc1_symbol_reachability              true
% 2.77/0.98  --bmc1_property_lemmas                  false
% 2.77/0.98  --bmc1_k_induction                      false
% 2.77/0.98  --bmc1_non_equiv_states                 false
% 2.77/0.98  --bmc1_deadlock                         false
% 2.77/0.98  --bmc1_ucm                              false
% 2.77/0.98  --bmc1_add_unsat_core                   none
% 2.77/0.98  --bmc1_unsat_core_children              false
% 2.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/0.98  --bmc1_out_stat                         full
% 2.77/0.98  --bmc1_ground_init                      false
% 2.77/0.98  --bmc1_pre_inst_next_state              false
% 2.77/0.98  --bmc1_pre_inst_state                   false
% 2.77/0.98  --bmc1_pre_inst_reach_state             false
% 2.77/0.98  --bmc1_out_unsat_core                   false
% 2.77/0.98  --bmc1_aig_witness_out                  false
% 2.77/0.98  --bmc1_verbose                          false
% 2.77/0.98  --bmc1_dump_clauses_tptp                false
% 2.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.77/0.98  --bmc1_dump_file                        -
% 2.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.77/0.98  --bmc1_ucm_extend_mode                  1
% 2.77/0.98  --bmc1_ucm_init_mode                    2
% 2.77/0.98  --bmc1_ucm_cone_mode                    none
% 2.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.77/0.98  --bmc1_ucm_relax_model                  4
% 2.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/0.98  --bmc1_ucm_layered_model                none
% 2.77/0.98  --bmc1_ucm_max_lemma_size               10
% 2.77/0.98  
% 2.77/0.98  ------ AIG Options
% 2.77/0.98  
% 2.77/0.98  --aig_mode                              false
% 2.77/0.98  
% 2.77/0.98  ------ Instantiation Options
% 2.77/0.98  
% 2.77/0.98  --instantiation_flag                    true
% 2.77/0.98  --inst_sos_flag                         false
% 2.77/0.98  --inst_sos_phase                        true
% 2.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel_side                     num_symb
% 2.77/0.98  --inst_solver_per_active                1400
% 2.77/0.98  --inst_solver_calls_frac                1.
% 2.77/0.98  --inst_passive_queue_type               priority_queues
% 2.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/0.98  --inst_passive_queues_freq              [25;2]
% 2.77/0.98  --inst_dismatching                      true
% 2.77/0.98  --inst_eager_unprocessed_to_passive     true
% 2.77/0.98  --inst_prop_sim_given                   true
% 2.77/0.98  --inst_prop_sim_new                     false
% 2.77/0.98  --inst_subs_new                         false
% 2.77/0.98  --inst_eq_res_simp                      false
% 2.77/0.98  --inst_subs_given                       false
% 2.77/0.98  --inst_orphan_elimination               true
% 2.77/0.98  --inst_learning_loop_flag               true
% 2.77/0.98  --inst_learning_start                   3000
% 2.77/0.98  --inst_learning_factor                  2
% 2.77/0.98  --inst_start_prop_sim_after_learn       3
% 2.77/0.98  --inst_sel_renew                        solver
% 2.77/0.98  --inst_lit_activity_flag                true
% 2.77/0.98  --inst_restr_to_given                   false
% 2.77/0.98  --inst_activity_threshold               500
% 2.77/0.98  --inst_out_proof                        true
% 2.77/0.98  
% 2.77/0.98  ------ Resolution Options
% 2.77/0.98  
% 2.77/0.98  --resolution_flag                       true
% 2.77/0.98  --res_lit_sel                           adaptive
% 2.77/0.98  --res_lit_sel_side                      none
% 2.77/0.98  --res_ordering                          kbo
% 2.77/0.98  --res_to_prop_solver                    active
% 2.77/0.98  --res_prop_simpl_new                    false
% 2.77/0.98  --res_prop_simpl_given                  true
% 2.77/0.98  --res_passive_queue_type                priority_queues
% 2.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/0.98  --res_passive_queues_freq               [15;5]
% 2.77/0.98  --res_forward_subs                      full
% 2.77/0.98  --res_backward_subs                     full
% 2.77/0.98  --res_forward_subs_resolution           true
% 2.77/0.98  --res_backward_subs_resolution          true
% 2.77/0.98  --res_orphan_elimination                true
% 2.77/0.98  --res_time_limit                        2.
% 2.77/0.98  --res_out_proof                         true
% 2.77/0.98  
% 2.77/0.98  ------ Superposition Options
% 2.77/0.98  
% 2.77/0.98  --superposition_flag                    true
% 2.77/0.98  --sup_passive_queue_type                priority_queues
% 2.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.77/0.98  --demod_completeness_check              fast
% 2.77/0.98  --demod_use_ground                      true
% 2.77/0.98  --sup_to_prop_solver                    passive
% 2.77/0.98  --sup_prop_simpl_new                    true
% 2.77/0.98  --sup_prop_simpl_given                  true
% 2.77/0.98  --sup_fun_splitting                     false
% 2.77/0.98  --sup_smt_interval                      50000
% 2.77/0.98  
% 2.77/0.98  ------ Superposition Simplification Setup
% 2.77/0.98  
% 2.77/0.98  --sup_indices_passive                   []
% 2.77/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_full_bw                           [BwDemod]
% 2.77/0.98  --sup_immed_triv                        [TrivRules]
% 2.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_immed_bw_main                     []
% 2.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.98  
% 2.77/0.98  ------ Combination Options
% 2.77/0.98  
% 2.77/0.98  --comb_res_mult                         3
% 2.77/0.98  --comb_sup_mult                         2
% 2.77/0.98  --comb_inst_mult                        10
% 2.77/0.98  
% 2.77/0.98  ------ Debug Options
% 2.77/0.98  
% 2.77/0.98  --dbg_backtrace                         false
% 2.77/0.98  --dbg_dump_prop_clauses                 false
% 2.77/0.98  --dbg_dump_prop_clauses_file            -
% 2.77/0.98  --dbg_out_stat                          false
% 2.77/0.98  ------ Parsing...
% 2.77/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/0.98  ------ Proving...
% 2.77/0.98  ------ Problem Properties 
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  clauses                                 24
% 2.77/0.98  conjectures                             6
% 2.77/0.98  EPR                                     6
% 2.77/0.98  Horn                                    19
% 2.77/0.98  unary                                   13
% 2.77/0.98  binary                                  5
% 2.77/0.98  lits                                    45
% 2.77/0.98  lits eq                                 37
% 2.77/0.98  fd_pure                                 0
% 2.77/0.98  fd_pseudo                               0
% 2.77/0.98  fd_cond                                 5
% 2.77/0.98  fd_pseudo_cond                          3
% 2.77/0.98  AC symbols                              0
% 2.77/0.98  
% 2.77/0.98  ------ Schedule dynamic 5 is on 
% 2.77/0.98  
% 2.77/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  ------ 
% 2.77/0.98  Current options:
% 2.77/0.98  ------ 
% 2.77/0.98  
% 2.77/0.98  ------ Input Options
% 2.77/0.98  
% 2.77/0.98  --out_options                           all
% 2.77/0.98  --tptp_safe_out                         true
% 2.77/0.98  --problem_path                          ""
% 2.77/0.98  --include_path                          ""
% 2.77/0.98  --clausifier                            res/vclausify_rel
% 2.77/0.98  --clausifier_options                    --mode clausify
% 2.77/0.98  --stdin                                 false
% 2.77/0.98  --stats_out                             all
% 2.77/0.98  
% 2.77/0.98  ------ General Options
% 2.77/0.98  
% 2.77/0.98  --fof                                   false
% 2.77/0.98  --time_out_real                         305.
% 2.77/0.98  --time_out_virtual                      -1.
% 2.77/0.98  --symbol_type_check                     false
% 2.77/0.98  --clausify_out                          false
% 2.77/0.98  --sig_cnt_out                           false
% 2.77/0.98  --trig_cnt_out                          false
% 2.77/0.98  --trig_cnt_out_tolerance                1.
% 2.77/0.98  --trig_cnt_out_sk_spl                   false
% 2.77/0.98  --abstr_cl_out                          false
% 2.77/0.98  
% 2.77/0.98  ------ Global Options
% 2.77/0.98  
% 2.77/0.98  --schedule                              default
% 2.77/0.98  --add_important_lit                     false
% 2.77/0.98  --prop_solver_per_cl                    1000
% 2.77/0.98  --min_unsat_core                        false
% 2.77/0.98  --soft_assumptions                      false
% 2.77/0.98  --soft_lemma_size                       3
% 2.77/0.98  --prop_impl_unit_size                   0
% 2.77/0.98  --prop_impl_unit                        []
% 2.77/0.98  --share_sel_clauses                     true
% 2.77/0.98  --reset_solvers                         false
% 2.77/0.98  --bc_imp_inh                            [conj_cone]
% 2.77/0.98  --conj_cone_tolerance                   3.
% 2.77/0.98  --extra_neg_conj                        none
% 2.77/0.98  --large_theory_mode                     true
% 2.77/0.98  --prolific_symb_bound                   200
% 2.77/0.98  --lt_threshold                          2000
% 2.77/0.98  --clause_weak_htbl                      true
% 2.77/0.98  --gc_record_bc_elim                     false
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing Options
% 2.77/0.98  
% 2.77/0.98  --preprocessing_flag                    true
% 2.77/0.98  --time_out_prep_mult                    0.1
% 2.77/0.98  --splitting_mode                        input
% 2.77/0.98  --splitting_grd                         true
% 2.77/0.98  --splitting_cvd                         false
% 2.77/0.98  --splitting_cvd_svl                     false
% 2.77/0.98  --splitting_nvd                         32
% 2.77/0.98  --sub_typing                            true
% 2.77/0.98  --prep_gs_sim                           true
% 2.77/0.98  --prep_unflatten                        true
% 2.77/0.98  --prep_res_sim                          true
% 2.77/0.98  --prep_upred                            true
% 2.77/0.98  --prep_sem_filter                       exhaustive
% 2.77/0.98  --prep_sem_filter_out                   false
% 2.77/0.98  --pred_elim                             true
% 2.77/0.98  --res_sim_input                         true
% 2.77/0.98  --eq_ax_congr_red                       true
% 2.77/0.98  --pure_diseq_elim                       true
% 2.77/0.98  --brand_transform                       false
% 2.77/0.98  --non_eq_to_eq                          false
% 2.77/0.98  --prep_def_merge                        true
% 2.77/0.98  --prep_def_merge_prop_impl              false
% 2.77/0.98  --prep_def_merge_mbd                    true
% 2.77/0.98  --prep_def_merge_tr_red                 false
% 2.77/0.98  --prep_def_merge_tr_cl                  false
% 2.77/0.98  --smt_preprocessing                     true
% 2.77/0.98  --smt_ac_axioms                         fast
% 2.77/0.98  --preprocessed_out                      false
% 2.77/0.98  --preprocessed_stats                    false
% 2.77/0.98  
% 2.77/0.98  ------ Abstraction refinement Options
% 2.77/0.98  
% 2.77/0.98  --abstr_ref                             []
% 2.77/0.98  --abstr_ref_prep                        false
% 2.77/0.98  --abstr_ref_until_sat                   false
% 2.77/0.98  --abstr_ref_sig_restrict                funpre
% 2.77/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/0.98  --abstr_ref_under                       []
% 2.77/0.98  
% 2.77/0.98  ------ SAT Options
% 2.77/0.98  
% 2.77/0.98  --sat_mode                              false
% 2.77/0.98  --sat_fm_restart_options                ""
% 2.77/0.98  --sat_gr_def                            false
% 2.77/0.98  --sat_epr_types                         true
% 2.77/0.98  --sat_non_cyclic_types                  false
% 2.77/0.98  --sat_finite_models                     false
% 2.77/0.98  --sat_fm_lemmas                         false
% 2.77/0.98  --sat_fm_prep                           false
% 2.77/0.98  --sat_fm_uc_incr                        true
% 2.77/0.98  --sat_out_model                         small
% 2.77/0.98  --sat_out_clauses                       false
% 2.77/0.98  
% 2.77/0.98  ------ QBF Options
% 2.77/0.98  
% 2.77/0.98  --qbf_mode                              false
% 2.77/0.98  --qbf_elim_univ                         false
% 2.77/0.98  --qbf_dom_inst                          none
% 2.77/0.98  --qbf_dom_pre_inst                      false
% 2.77/0.98  --qbf_sk_in                             false
% 2.77/0.98  --qbf_pred_elim                         true
% 2.77/0.98  --qbf_split                             512
% 2.77/0.98  
% 2.77/0.98  ------ BMC1 Options
% 2.77/0.98  
% 2.77/0.98  --bmc1_incremental                      false
% 2.77/0.98  --bmc1_axioms                           reachable_all
% 2.77/0.98  --bmc1_min_bound                        0
% 2.77/0.98  --bmc1_max_bound                        -1
% 2.77/0.98  --bmc1_max_bound_default                -1
% 2.77/0.98  --bmc1_symbol_reachability              true
% 2.77/0.98  --bmc1_property_lemmas                  false
% 2.77/0.98  --bmc1_k_induction                      false
% 2.77/0.98  --bmc1_non_equiv_states                 false
% 2.77/0.98  --bmc1_deadlock                         false
% 2.77/0.98  --bmc1_ucm                              false
% 2.77/0.98  --bmc1_add_unsat_core                   none
% 2.77/0.98  --bmc1_unsat_core_children              false
% 2.77/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/0.98  --bmc1_out_stat                         full
% 2.77/0.98  --bmc1_ground_init                      false
% 2.77/0.98  --bmc1_pre_inst_next_state              false
% 2.77/0.98  --bmc1_pre_inst_state                   false
% 2.77/0.98  --bmc1_pre_inst_reach_state             false
% 2.77/0.98  --bmc1_out_unsat_core                   false
% 2.77/0.98  --bmc1_aig_witness_out                  false
% 2.77/0.98  --bmc1_verbose                          false
% 2.77/0.98  --bmc1_dump_clauses_tptp                false
% 2.77/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.77/0.98  --bmc1_dump_file                        -
% 2.77/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.77/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.77/0.98  --bmc1_ucm_extend_mode                  1
% 2.77/0.98  --bmc1_ucm_init_mode                    2
% 2.77/0.98  --bmc1_ucm_cone_mode                    none
% 2.77/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.77/0.98  --bmc1_ucm_relax_model                  4
% 2.77/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.77/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/0.98  --bmc1_ucm_layered_model                none
% 2.77/0.98  --bmc1_ucm_max_lemma_size               10
% 2.77/0.98  
% 2.77/0.98  ------ AIG Options
% 2.77/0.98  
% 2.77/0.98  --aig_mode                              false
% 2.77/0.98  
% 2.77/0.98  ------ Instantiation Options
% 2.77/0.98  
% 2.77/0.98  --instantiation_flag                    true
% 2.77/0.98  --inst_sos_flag                         false
% 2.77/0.98  --inst_sos_phase                        true
% 2.77/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/0.98  --inst_lit_sel_side                     none
% 2.77/0.98  --inst_solver_per_active                1400
% 2.77/0.98  --inst_solver_calls_frac                1.
% 2.77/0.98  --inst_passive_queue_type               priority_queues
% 2.77/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/0.98  --inst_passive_queues_freq              [25;2]
% 2.77/0.98  --inst_dismatching                      true
% 2.77/0.98  --inst_eager_unprocessed_to_passive     true
% 2.77/0.98  --inst_prop_sim_given                   true
% 2.77/0.98  --inst_prop_sim_new                     false
% 2.77/0.98  --inst_subs_new                         false
% 2.77/0.98  --inst_eq_res_simp                      false
% 2.77/0.98  --inst_subs_given                       false
% 2.77/0.98  --inst_orphan_elimination               true
% 2.77/0.98  --inst_learning_loop_flag               true
% 2.77/0.98  --inst_learning_start                   3000
% 2.77/0.98  --inst_learning_factor                  2
% 2.77/0.98  --inst_start_prop_sim_after_learn       3
% 2.77/0.98  --inst_sel_renew                        solver
% 2.77/0.98  --inst_lit_activity_flag                true
% 2.77/0.98  --inst_restr_to_given                   false
% 2.77/0.98  --inst_activity_threshold               500
% 2.77/0.98  --inst_out_proof                        true
% 2.77/0.98  
% 2.77/0.98  ------ Resolution Options
% 2.77/0.98  
% 2.77/0.98  --resolution_flag                       false
% 2.77/0.98  --res_lit_sel                           adaptive
% 2.77/0.98  --res_lit_sel_side                      none
% 2.77/0.98  --res_ordering                          kbo
% 2.77/0.98  --res_to_prop_solver                    active
% 2.77/0.98  --res_prop_simpl_new                    false
% 2.77/0.98  --res_prop_simpl_given                  true
% 2.77/0.98  --res_passive_queue_type                priority_queues
% 2.77/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/0.98  --res_passive_queues_freq               [15;5]
% 2.77/0.98  --res_forward_subs                      full
% 2.77/0.98  --res_backward_subs                     full
% 2.77/0.98  --res_forward_subs_resolution           true
% 2.77/0.98  --res_backward_subs_resolution          true
% 2.77/0.98  --res_orphan_elimination                true
% 2.77/0.98  --res_time_limit                        2.
% 2.77/0.98  --res_out_proof                         true
% 2.77/0.98  
% 2.77/0.98  ------ Superposition Options
% 2.77/0.98  
% 2.77/0.98  --superposition_flag                    true
% 2.77/0.98  --sup_passive_queue_type                priority_queues
% 2.77/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.77/0.98  --demod_completeness_check              fast
% 2.77/0.98  --demod_use_ground                      true
% 2.77/0.98  --sup_to_prop_solver                    passive
% 2.77/0.98  --sup_prop_simpl_new                    true
% 2.77/0.98  --sup_prop_simpl_given                  true
% 2.77/0.98  --sup_fun_splitting                     false
% 2.77/0.98  --sup_smt_interval                      50000
% 2.77/0.98  
% 2.77/0.98  ------ Superposition Simplification Setup
% 2.77/0.98  
% 2.77/0.98  --sup_indices_passive                   []
% 2.77/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_full_bw                           [BwDemod]
% 2.77/0.98  --sup_immed_triv                        [TrivRules]
% 2.77/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_immed_bw_main                     []
% 2.77/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/0.98  
% 2.77/0.98  ------ Combination Options
% 2.77/0.98  
% 2.77/0.98  --comb_res_mult                         3
% 2.77/0.98  --comb_sup_mult                         2
% 2.77/0.98  --comb_inst_mult                        10
% 2.77/0.98  
% 2.77/0.98  ------ Debug Options
% 2.77/0.98  
% 2.77/0.98  --dbg_backtrace                         false
% 2.77/0.98  --dbg_dump_prop_clauses                 false
% 2.77/0.98  --dbg_dump_prop_clauses_file            -
% 2.77/0.98  --dbg_out_stat                          false
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  ------ Proving...
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  % SZS status Theorem for theBenchmark.p
% 2.77/0.98  
% 2.77/0.98   Resolution empty clause
% 2.77/0.98  
% 2.77/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/0.98  
% 2.77/0.98  fof(f9,conjecture,(
% 2.77/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.98  
% 2.77/0.98  fof(f10,negated_conjecture,(
% 2.77/0.98    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.77/0.98    inference(negated_conjecture,[],[f9])).
% 2.77/0.98  
% 2.77/0.98  fof(f15,plain,(
% 2.77/0.98    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 2.77/0.98    inference(ennf_transformation,[],[f10])).
% 2.77/0.98  
% 2.77/0.98  fof(f16,plain,(
% 2.77/0.98    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 2.77/0.98    inference(flattening,[],[f15])).
% 2.77/0.98  
% 2.77/0.98  fof(f21,plain,(
% 2.77/0.98    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 2.77/0.98    introduced(choice_axiom,[])).
% 2.77/0.98  
% 2.77/0.98  fof(f22,plain,(
% 2.77/0.98    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 2.77/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f21])).
% 2.77/0.98  
% 2.77/0.98  fof(f43,plain,(
% 2.77/0.98    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 2.77/0.98    inference(cnf_transformation,[],[f22])).
% 2.77/0.98  
% 2.77/0.98  fof(f4,axiom,(
% 2.77/0.98    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 2.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.98  
% 2.77/0.98  fof(f27,plain,(
% 2.77/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f4])).
% 2.77/0.98  
% 2.77/0.98  fof(f3,axiom,(
% 2.77/0.98    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 2.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.98  
% 2.77/0.98  fof(f26,plain,(
% 2.77/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f3])).
% 2.77/0.98  
% 2.77/0.98  fof(f49,plain,(
% 2.77/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.77/0.98    inference(definition_unfolding,[],[f27,f26])).
% 2.77/0.98  
% 2.77/0.98  fof(f65,plain,(
% 2.77/0.98    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 2.77/0.98    inference(definition_unfolding,[],[f43,f49,f49])).
% 2.77/0.98  
% 2.77/0.98  fof(f6,axiom,(
% 2.77/0.98    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 2.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.98  
% 2.77/0.98  fof(f12,plain,(
% 2.77/0.98    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 2.77/0.98    inference(ennf_transformation,[],[f6])).
% 2.77/0.98  
% 2.77/0.98  fof(f13,plain,(
% 2.77/0.98    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 2.77/0.98    inference(flattening,[],[f12])).
% 2.77/0.98  
% 2.77/0.98  fof(f32,plain,(
% 2.77/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f13])).
% 2.77/0.98  
% 2.77/0.98  fof(f56,plain,(
% 2.77/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 2.77/0.98    inference(definition_unfolding,[],[f32,f26,f26,f26])).
% 2.77/0.98  
% 2.77/0.98  fof(f44,plain,(
% 2.77/0.98    k1_xboole_0 != sK0),
% 2.77/0.98    inference(cnf_transformation,[],[f22])).
% 2.77/0.98  
% 2.77/0.98  fof(f45,plain,(
% 2.77/0.98    k1_xboole_0 != sK1),
% 2.77/0.98    inference(cnf_transformation,[],[f22])).
% 2.77/0.98  
% 2.77/0.98  fof(f46,plain,(
% 2.77/0.98    k1_xboole_0 != sK2),
% 2.77/0.98    inference(cnf_transformation,[],[f22])).
% 2.77/0.98  
% 2.77/0.98  fof(f47,plain,(
% 2.77/0.98    k1_xboole_0 != sK3),
% 2.77/0.98    inference(cnf_transformation,[],[f22])).
% 2.77/0.98  
% 2.77/0.98  fof(f8,axiom,(
% 2.77/0.98    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 2.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.98  
% 2.77/0.98  fof(f19,plain,(
% 2.77/0.98    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.77/0.98    inference(nnf_transformation,[],[f8])).
% 2.77/0.98  
% 2.77/0.98  fof(f20,plain,(
% 2.77/0.98    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.77/0.98    inference(flattening,[],[f19])).
% 2.77/0.98  
% 2.77/0.98  fof(f38,plain,(
% 2.77/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.77/0.98    inference(cnf_transformation,[],[f20])).
% 2.77/0.98  
% 2.77/0.98  fof(f64,plain,(
% 2.77/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.77/0.98    inference(definition_unfolding,[],[f38,f49])).
% 2.77/0.98  
% 2.77/0.98  fof(f33,plain,(
% 2.77/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f13])).
% 2.77/0.98  
% 2.77/0.98  fof(f55,plain,(
% 2.77/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 2.77/0.98    inference(definition_unfolding,[],[f33,f26,f26,f26])).
% 2.77/0.98  
% 2.77/0.98  fof(f34,plain,(
% 2.77/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f13])).
% 2.77/0.98  
% 2.77/0.98  fof(f54,plain,(
% 2.77/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 2.77/0.98    inference(definition_unfolding,[],[f34,f26,f26,f26])).
% 2.77/0.98  
% 2.77/0.98  fof(f48,plain,(
% 2.77/0.98    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 2.77/0.98    inference(cnf_transformation,[],[f22])).
% 2.77/0.98  
% 2.77/0.98  fof(f5,axiom,(
% 2.77/0.98    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 2.77/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.98  
% 2.77/0.98  fof(f17,plain,(
% 2.77/0.98    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.77/0.98    inference(nnf_transformation,[],[f5])).
% 2.77/0.98  
% 2.77/0.98  fof(f18,plain,(
% 2.77/0.98    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.77/0.98    inference(flattening,[],[f17])).
% 2.77/0.98  
% 2.77/0.98  fof(f31,plain,(
% 2.77/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f18])).
% 2.77/0.98  
% 2.77/0.98  fof(f50,plain,(
% 2.77/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.77/0.98    inference(definition_unfolding,[],[f31,f26])).
% 2.77/0.98  
% 2.77/0.98  fof(f66,plain,(
% 2.77/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0)) )),
% 2.77/0.98    inference(equality_resolution,[],[f50])).
% 2.77/0.98  
% 2.77/0.98  fof(f39,plain,(
% 2.77/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f20])).
% 2.77/0.98  
% 2.77/0.98  fof(f63,plain,(
% 2.77/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.77/0.98    inference(definition_unfolding,[],[f39,f49])).
% 2.77/0.98  
% 2.77/0.98  fof(f72,plain,(
% 2.77/0.98    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 2.77/0.98    inference(equality_resolution,[],[f63])).
% 2.77/0.98  
% 2.77/0.98  fof(f29,plain,(
% 2.77/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 2.77/0.98    inference(cnf_transformation,[],[f18])).
% 2.77/0.98  
% 2.77/0.98  fof(f52,plain,(
% 2.77/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.77/0.98    inference(definition_unfolding,[],[f29,f26])).
% 2.77/0.98  
% 2.77/0.98  fof(f68,plain,(
% 2.77/0.98    ( ! [X2,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)) )),
% 2.77/0.98    inference(equality_resolution,[],[f52])).
% 2.77/0.98  
% 2.77/0.98  cnf(c_23,negated_conjecture,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
% 2.77/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_9,plain,
% 2.77/0.98      ( X0 = X1
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5) = k1_xboole_0 ),
% 2.77/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1258,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 2.77/0.98      | k2_zfmisc_1(sK4,sK5) = X0 ),
% 2.77/0.98      inference(superposition,[status(thm)],[c_23,c_9]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1672,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 2.77/0.98      | k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1) ),
% 2.77/0.98      inference(equality_resolution,[status(thm)],[c_1258]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_22,negated_conjecture,
% 2.77/0.98      ( k1_xboole_0 != sK0 ),
% 2.77/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_21,negated_conjecture,
% 2.77/0.98      ( k1_xboole_0 != sK1 ),
% 2.77/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_20,negated_conjecture,
% 2.77/0.98      ( k1_xboole_0 != sK2 ),
% 2.77/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_19,negated_conjecture,
% 2.77/0.98      ( k1_xboole_0 != sK3 ),
% 2.77/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_17,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 2.77/0.98      | k1_xboole_0 = X2
% 2.77/0.98      | k1_xboole_0 = X1
% 2.77/0.98      | k1_xboole_0 = X0
% 2.77/0.98      | k1_xboole_0 = X3 ),
% 2.77/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_396,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK2),X2) != k1_xboole_0
% 2.77/0.98      | k1_xboole_0 = X1
% 2.77/0.98      | k1_xboole_0 = X2
% 2.77/0.98      | k1_xboole_0 = X0
% 2.77/0.98      | k1_xboole_0 = sK2 ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_541,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),sK2),X1) != k1_xboole_0
% 2.77/0.98      | k1_xboole_0 = X1
% 2.77/0.98      | k1_xboole_0 = X0
% 2.77/0.98      | k1_xboole_0 = sK1
% 2.77/0.98      | k1_xboole_0 = sK2 ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_396]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_832,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),sK2),sK3) != k1_xboole_0
% 2.77/0.98      | k1_xboole_0 = X0
% 2.77/0.98      | k1_xboole_0 = sK1
% 2.77/0.98      | k1_xboole_0 = sK2
% 2.77/0.98      | k1_xboole_0 = sK3 ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_541]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1811,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0
% 2.77/0.98      | k1_xboole_0 = sK0
% 2.77/0.98      | k1_xboole_0 = sK1
% 2.77/0.98      | k1_xboole_0 = sK2
% 2.77/0.98      | k1_xboole_0 = sK3 ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_832]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_5419,plain,
% 2.77/0.98      ( k2_zfmisc_1(sK4,sK5) = k2_zfmisc_1(sK0,sK1) ),
% 2.77/0.98      inference(global_propositional_subsumption,
% 2.77/0.98                [status(thm)],
% 2.77/0.98                [c_1672,c_22,c_21,c_20,c_19,c_1811]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_8,plain,
% 2.77/0.98      ( X0 = X1
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = k1_xboole_0 ),
% 2.77/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_5460,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3)
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 2.77/0.98      | sK5 = X1 ),
% 2.77/0.98      inference(superposition,[status(thm)],[c_5419,c_8]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_5711,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) = k1_xboole_0 | sK5 = sK1 ),
% 2.77/0.98      inference(equality_resolution,[status(thm)],[c_5460]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_7,plain,
% 2.77/0.98      ( X0 = X1
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = k1_xboole_0 ),
% 2.77/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_745,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 2.77/0.98      | sK7 = X2 ),
% 2.77/0.98      inference(superposition,[status(thm)],[c_23,c_7]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_921,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 2.77/0.98      | sK7 = sK3 ),
% 2.77/0.98      inference(equality_resolution,[status(thm)],[c_745]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_4415,plain,
% 2.77/0.98      ( sK7 = sK3 ),
% 2.77/0.98      inference(global_propositional_subsumption,
% 2.77/0.98                [status(thm)],
% 2.77/0.98                [c_921,c_22,c_21,c_20,c_19,c_1811]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_18,negated_conjecture,
% 2.77/0.98      ( sK0 != sK4 | sK1 != sK5 | sK2 != sK6 | sK3 != sK7 ),
% 2.77/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_4438,plain,
% 2.77/0.98      ( sK4 != sK0 | sK5 != sK1 | sK6 != sK2 | sK3 != sK3 ),
% 2.77/0.98      inference(demodulation,[status(thm)],[c_4415,c_18]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_4442,plain,
% 2.77/0.98      ( sK4 != sK0 | sK5 != sK1 | sK6 != sK2 ),
% 2.77/0.98      inference(equality_resolution_simp,[status(thm)],[c_4438]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1183,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 2.77/0.98      | sK6 = X1 ),
% 2.77/0.98      inference(superposition,[status(thm)],[c_23,c_8]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1493,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 2.77/0.98      | sK6 = sK2 ),
% 2.77/0.98      inference(equality_resolution,[status(thm)],[c_1183]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_4678,plain,
% 2.77/0.98      ( sK5 != sK1 | sK4 != sK0 ),
% 2.77/0.98      inference(global_propositional_subsumption,
% 2.77/0.98                [status(thm)],
% 2.77/0.98                [c_4442,c_22,c_21,c_20,c_19,c_1493,c_1811]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_4679,plain,
% 2.77/0.98      ( sK4 != sK0 | sK5 != sK1 ),
% 2.77/0.98      inference(renaming,[status(thm)],[c_4678]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_5469,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3)
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 2.77/0.98      | sK4 = X0 ),
% 2.77/0.98      inference(superposition,[status(thm)],[c_5419,c_9]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_5741,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) = k1_xboole_0 | sK4 = sK0 ),
% 2.77/0.98      inference(equality_resolution,[status(thm)],[c_5469]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_6837,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) = k1_xboole_0 ),
% 2.77/0.98      inference(global_propositional_subsumption,
% 2.77/0.98                [status(thm)],
% 2.77/0.98                [c_5711,c_4679,c_5741]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_3,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
% 2.77/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_752,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 2.77/0.98      | sK7 = X2 ),
% 2.77/0.98      inference(superposition,[status(thm)],[c_23,c_7]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_780,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 2.77/0.98      | sK7 = X2 ),
% 2.77/0.98      inference(demodulation,[status(thm)],[c_752,c_23]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1037,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),X0) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
% 2.77/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 2.77/0.98      | sK7 = X0 ),
% 2.77/0.98      inference(superposition,[status(thm)],[c_23,c_780]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_2467,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),X0) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
% 2.77/0.98      | sK7 = X0 ),
% 2.77/0.98      inference(global_propositional_subsumption,
% 2.77/0.98                [status(thm)],
% 2.77/0.98                [c_1037,c_22,c_21,c_20,c_19,c_1811]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_2472,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0
% 2.77/0.98      | sK7 = k1_xboole_0 ),
% 2.77/0.98      inference(superposition,[status(thm)],[c_3,c_2467]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_2584,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0 ),
% 2.77/0.98      inference(global_propositional_subsumption,
% 2.77/0.98                [status(thm)],
% 2.77/0.98                [c_2472,c_22,c_21,c_20,c_19,c_1811]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_6853,plain,
% 2.77/0.98      ( k2_zfmisc_1(k1_xboole_0,sK3) != k1_xboole_0 ),
% 2.77/0.98      inference(demodulation,[status(thm)],[c_6837,c_2584]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_16,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 2.77/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_5,plain,
% 2.77/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) = k1_xboole_0 ),
% 2.77/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_231,plain,
% 2.77/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.77/0.98      inference(light_normalisation,[status(thm)],[c_16,c_5]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_6870,plain,
% 2.77/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 2.77/0.98      inference(demodulation,[status(thm)],[c_6853,c_231]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_6871,plain,
% 2.77/0.98      ( $false ),
% 2.77/0.98      inference(equality_resolution_simp,[status(thm)],[c_6870]) ).
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/0.98  
% 2.77/0.98  ------                               Statistics
% 2.77/0.98  
% 2.77/0.98  ------ General
% 2.77/0.98  
% 2.77/0.98  abstr_ref_over_cycles:                  0
% 2.77/0.98  abstr_ref_under_cycles:                 0
% 2.77/0.98  gc_basic_clause_elim:                   0
% 2.77/0.98  forced_gc_time:                         0
% 2.77/0.98  parsing_time:                           0.009
% 2.77/0.98  unif_index_cands_time:                  0.
% 2.77/0.98  unif_index_add_time:                    0.
% 2.77/0.98  orderings_time:                         0.
% 2.77/0.98  out_proof_time:                         0.007
% 2.77/0.98  total_time:                             0.285
% 2.77/0.98  num_of_symbols:                         42
% 2.77/0.98  num_of_terms:                           14347
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing
% 2.77/0.98  
% 2.77/0.98  num_of_splits:                          0
% 2.77/0.98  num_of_split_atoms:                     0
% 2.77/0.98  num_of_reused_defs:                     0
% 2.77/0.98  num_eq_ax_congr_red:                    0
% 2.77/0.98  num_of_sem_filtered_clauses:            1
% 2.77/0.98  num_of_subtypes:                        0
% 2.77/0.98  monotx_restored_types:                  0
% 2.77/0.98  sat_num_of_epr_types:                   0
% 2.77/0.98  sat_num_of_non_cyclic_types:            0
% 2.77/0.98  sat_guarded_non_collapsed_types:        0
% 2.77/0.98  num_pure_diseq_elim:                    0
% 2.77/0.98  simp_replaced_by:                       0
% 2.77/0.98  res_preprocessed:                       81
% 2.77/0.98  prep_upred:                             0
% 2.77/0.98  prep_unflattend:                        0
% 2.77/0.98  smt_new_axioms:                         0
% 2.77/0.98  pred_elim_cands:                        1
% 2.77/0.98  pred_elim:                              0
% 2.77/0.98  pred_elim_cl:                           0
% 2.77/0.98  pred_elim_cycles:                       1
% 2.77/0.98  merged_defs:                            0
% 2.77/0.98  merged_defs_ncl:                        0
% 2.77/0.98  bin_hyper_res:                          0
% 2.77/0.98  prep_cycles:                            3
% 2.77/0.98  pred_elim_time:                         0.
% 2.77/0.98  splitting_time:                         0.
% 2.77/0.98  sem_filter_time:                        0.
% 2.77/0.98  monotx_time:                            0.
% 2.77/0.98  subtype_inf_time:                       0.
% 2.77/0.98  
% 2.77/0.98  ------ Problem properties
% 2.77/0.98  
% 2.77/0.98  clauses:                                24
% 2.77/0.98  conjectures:                            6
% 2.77/0.98  epr:                                    6
% 2.77/0.98  horn:                                   19
% 2.77/0.98  ground:                                 6
% 2.77/0.98  unary:                                  13
% 2.77/0.98  binary:                                 5
% 2.77/0.98  lits:                                   45
% 2.77/0.98  lits_eq:                                37
% 2.77/0.98  fd_pure:                                0
% 2.77/0.98  fd_pseudo:                              0
% 2.77/0.98  fd_cond:                                5
% 2.77/0.98  fd_pseudo_cond:                         3
% 2.77/0.98  ac_symbols:                             0
% 2.77/0.98  
% 2.77/0.98  ------ Propositional Solver
% 2.77/0.98  
% 2.77/0.98  prop_solver_calls:                      25
% 2.77/0.98  prop_fast_solver_calls:                 695
% 2.77/0.98  smt_solver_calls:                       0
% 2.77/0.98  smt_fast_solver_calls:                  0
% 2.77/0.98  prop_num_of_clauses:                    3028
% 2.77/0.98  prop_preprocess_simplified:             11032
% 2.77/0.98  prop_fo_subsumed:                       40
% 2.77/0.98  prop_solver_time:                       0.
% 2.77/0.98  smt_solver_time:                        0.
% 2.77/0.98  smt_fast_solver_time:                   0.
% 2.77/0.98  prop_fast_solver_time:                  0.
% 2.77/0.98  prop_unsat_core_time:                   0.
% 2.77/0.98  
% 2.77/0.98  ------ QBF
% 2.77/0.98  
% 2.77/0.98  qbf_q_res:                              0
% 2.77/0.98  qbf_num_tautologies:                    0
% 2.77/0.98  qbf_prep_cycles:                        0
% 2.77/0.98  
% 2.77/0.98  ------ BMC1
% 2.77/0.98  
% 2.77/0.98  bmc1_current_bound:                     -1
% 2.77/0.98  bmc1_last_solved_bound:                 -1
% 2.77/0.98  bmc1_unsat_core_size:                   -1
% 2.77/0.98  bmc1_unsat_core_parents_size:           -1
% 2.77/0.98  bmc1_merge_next_fun:                    0
% 2.77/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.77/0.98  
% 2.77/0.98  ------ Instantiation
% 2.77/0.98  
% 2.77/0.98  inst_num_of_clauses:                    2175
% 2.77/0.98  inst_num_in_passive:                    1561
% 2.77/0.98  inst_num_in_active:                     529
% 2.77/0.98  inst_num_in_unprocessed:                85
% 2.77/0.98  inst_num_of_loops:                      530
% 2.77/0.98  inst_num_of_learning_restarts:          0
% 2.77/0.98  inst_num_moves_active_passive:          1
% 2.77/0.98  inst_lit_activity:                      0
% 2.77/0.98  inst_lit_activity_moves:                0
% 2.77/0.98  inst_num_tautologies:                   0
% 2.77/0.98  inst_num_prop_implied:                  0
% 2.77/0.98  inst_num_existing_simplified:           0
% 2.77/0.98  inst_num_eq_res_simplified:             0
% 2.77/0.98  inst_num_child_elim:                    0
% 2.77/0.98  inst_num_of_dismatching_blockings:      4
% 2.77/0.98  inst_num_of_non_proper_insts:           1279
% 2.77/0.98  inst_num_of_duplicates:                 0
% 2.77/0.98  inst_inst_num_from_inst_to_res:         0
% 2.77/0.98  inst_dismatching_checking_time:         0.
% 2.77/0.98  
% 2.77/0.98  ------ Resolution
% 2.77/0.98  
% 2.77/0.98  res_num_of_clauses:                     0
% 2.77/0.98  res_num_in_passive:                     0
% 2.77/0.98  res_num_in_active:                      0
% 2.77/0.98  res_num_of_loops:                       84
% 2.77/0.98  res_forward_subset_subsumed:            105
% 2.77/0.98  res_backward_subset_subsumed:           0
% 2.77/0.98  res_forward_subsumed:                   0
% 2.77/0.98  res_backward_subsumed:                  0
% 2.77/0.98  res_forward_subsumption_resolution:     0
% 2.77/0.98  res_backward_subsumption_resolution:    0
% 2.77/0.98  res_clause_to_clause_subsumption:       1302
% 2.77/0.98  res_orphan_elimination:                 0
% 2.77/0.98  res_tautology_del:                      1
% 2.77/0.98  res_num_eq_res_simplified:              0
% 2.77/0.98  res_num_sel_changes:                    0
% 2.77/0.98  res_moves_from_active_to_pass:          0
% 2.77/0.98  
% 2.77/0.98  ------ Superposition
% 2.77/0.98  
% 2.77/0.98  sup_time_total:                         0.
% 2.77/0.98  sup_time_generating:                    0.
% 2.77/0.98  sup_time_sim_full:                      0.
% 2.77/0.98  sup_time_sim_immed:                     0.
% 2.77/0.98  
% 2.77/0.98  sup_num_of_clauses:                     93
% 2.77/0.98  sup_num_in_active:                      35
% 2.77/0.98  sup_num_in_passive:                     58
% 2.77/0.98  sup_num_of_loops:                       105
% 2.77/0.98  sup_fw_superposition:                   352
% 2.77/0.98  sup_bw_superposition:                   1219
% 2.77/0.98  sup_immediate_simplified:               810
% 2.77/0.98  sup_given_eliminated:                   0
% 2.77/0.98  comparisons_done:                       0
% 2.77/0.98  comparisons_avoided:                    0
% 2.77/0.98  
% 2.77/0.98  ------ Simplifications
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  sim_fw_subset_subsumed:                 355
% 2.77/0.98  sim_bw_subset_subsumed:                 7
% 2.77/0.98  sim_fw_subsumed:                        331
% 2.77/0.98  sim_bw_subsumed:                        4
% 2.77/0.98  sim_fw_subsumption_res:                 0
% 2.77/0.98  sim_bw_subsumption_res:                 0
% 2.77/0.98  sim_tautology_del:                      117
% 2.77/0.98  sim_eq_tautology_del:                   119
% 2.77/0.98  sim_eq_res_simp:                        9
% 2.77/0.98  sim_fw_demodulated:                     123
% 2.77/0.98  sim_bw_demodulated:                     67
% 2.77/0.98  sim_light_normalised:                   66
% 2.77/0.98  sim_joinable_taut:                      0
% 2.77/0.98  sim_joinable_simp:                      0
% 2.77/0.98  sim_ac_normalised:                      0
% 2.77/0.98  sim_smt_subsumption:                    0
% 2.77/0.98  
%------------------------------------------------------------------------------
