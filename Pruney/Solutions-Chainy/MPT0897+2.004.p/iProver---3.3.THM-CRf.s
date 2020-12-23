%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:41 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  150 (1772 expanded)
%              Number of clauses        :  103 ( 424 expanded)
%              Number of leaves         :   16 ( 527 expanded)
%              Depth                    :   18
%              Number of atoms          :  409 (4991 expanded)
%              Number of equality atoms :  319 (4707 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f14])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f38,f32,f32,f32])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f16])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK5 != sK9
        | sK4 != sK8
        | sK3 != sK7
        | sK2 != sK6 )
      & k1_xboole_0 != k4_zfmisc_1(sK2,sK3,sK4,sK5)
      & k4_zfmisc_1(sK2,sK3,sK4,sK5) = k4_zfmisc_1(sK6,sK7,sK8,sK9) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( sK5 != sK9
      | sK4 != sK8
      | sK3 != sK7
      | sK2 != sK6 )
    & k1_xboole_0 != k4_zfmisc_1(sK2,sK3,sK4,sK5)
    & k4_zfmisc_1(sK2,sK3,sK4,sK5) = k4_zfmisc_1(sK6,sK7,sK8,sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f17,f24])).

fof(f39,plain,(
    k4_zfmisc_1(sK2,sK3,sK4,sK5) = k4_zfmisc_1(sK6,sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f47,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) ),
    inference(definition_unfolding,[],[f39,f42,f42])).

fof(f40,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,
    ( sK5 != sK9
    | sK4 != sK8
    | sK3 != sK7
    | sK2 != sK6 ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f37,f32,f32,f32])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK1) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f22])).

fof(f29,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f36,f32,f32,f32])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1339,plain,
    ( r2_hidden(k1_mcart_1(sK0(k2_zfmisc_1(X0,X1))),X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[status(thm)],[c_7,c_0])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3551,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[status(thm)],[c_1339,c_1])).

cnf(c_136,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_134,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1871,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
    | v1_xboole_0(k2_zfmisc_1(X2,X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_136,c_134])).

cnf(c_8,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_13,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1946,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) = k1_xboole_0
    | sK5 = sK9 ),
    inference(resolution,[status(thm)],[c_8,c_13])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_132,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_145,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_133,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_391,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_453,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_393,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK9) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK9)
    | sK5 = sK9 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_468,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)
    | sK5 = sK9 ),
    inference(instantiation,[status(thm)],[c_393])).

cnf(c_495,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_496,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_1950,plain,
    ( sK5 = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1946,c_13,c_12,c_145,c_453,c_468,c_496])).

cnf(c_7068,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X0,sK9))
    | v1_xboole_0(k2_zfmisc_1(X1,sK5))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_1871,c_1950])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11737,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_zfmisc_1(X0,sK9))
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5)) ),
    inference(resolution,[status(thm)],[c_7068,c_2])).

cnf(c_13019,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3551,c_11737])).

cnf(c_13021,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13019])).

cnf(c_432,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5))
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_11284,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X0,sK9))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5))
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(X0,sK9) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_11287,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5))
    | ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK9))
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k1_xboole_0,sK9) ),
    inference(instantiation,[status(thm)],[c_11284])).

cnf(c_5,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_679,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5)) = k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)
    | sK9 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_5])).

cnf(c_1154,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_679])).

cnf(c_446,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_636,plain,
    ( X0 != sK9
    | sK5 = X0
    | sK5 != sK9 ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_637,plain,
    ( sK5 != sK9
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK9 ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_1142,plain,
    ( X0 != X1
    | X0 = sK9
    | sK9 != X1 ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_1143,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_2622,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1154,c_13,c_12,c_145,c_453,c_468,c_496,c_637,c_1143])).

cnf(c_2623,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2622])).

cnf(c_4,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2632,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k2_zfmisc_1(sK6,sK7) = k1_xboole_0
    | k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = sK8
    | sK8 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2623,c_4])).

cnf(c_826,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK9 = X2 ),
    inference(superposition,[status(thm)],[c_13,c_8])).

cnf(c_392,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_828,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK9 = X2 ),
    inference(superposition,[status(thm)],[c_13,c_8])).

cnf(c_841,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k1_xboole_0
    | sK9 = X2 ),
    inference(demodulation,[status(thm)],[c_828,c_13])).

cnf(c_1156,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK9 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_826,c_12,c_145,c_392,c_841])).

cnf(c_1163,plain,
    ( sK9 = sK5 ),
    inference(equality_resolution,[status(thm)],[c_1156])).

cnf(c_11,negated_conjecture,
    ( sK2 != sK6
    | sK3 != sK7
    | sK4 != sK8
    | sK5 != sK9 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3445,plain,
    ( sK6 != sK2
    | sK7 != sK3
    | sK8 != sK4
    | sK5 != sK5 ),
    inference(demodulation,[status(thm)],[c_1163,c_11])).

cnf(c_3449,plain,
    ( sK6 != sK2
    | sK7 != sK3
    | sK8 != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_3445])).

cnf(c_9,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_862,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK8 = X1 ),
    inference(superposition,[status(thm)],[c_13,c_9])).

cnf(c_864,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK8 = X1 ),
    inference(superposition,[status(thm)],[c_13,c_9])).

cnf(c_877,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k1_xboole_0
    | sK8 = X1 ),
    inference(demodulation,[status(thm)],[c_864,c_13])).

cnf(c_1285,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | sK8 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_862,c_12,c_145,c_392,c_877])).

cnf(c_1292,plain,
    ( sK8 = sK4 ),
    inference(equality_resolution,[status(thm)],[c_1285])).

cnf(c_3953,plain,
    ( sK7 != sK3
    | sK6 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3449,c_1292])).

cnf(c_3954,plain,
    ( sK6 != sK2
    | sK7 != sK3 ),
    inference(renaming,[status(thm)],[c_3953])).

cnf(c_2645,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK7 = X1
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2623,c_9])).

cnf(c_3,plain,
    ( v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_276,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_277,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_500,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_276,c_277])).

cnf(c_502,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_500,c_276])).

cnf(c_503,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_502])).

cnf(c_902,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_913,plain,
    ( r2_hidden(k2_mcart_1(sK0(k2_zfmisc_1(X0,X1))),X1)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[status(thm)],[c_6,c_0])).

cnf(c_1522,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_913,c_1])).

cnf(c_1735,plain,
    ( ~ v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_902,c_1522])).

cnf(c_1960,plain,
    ( ~ v1_xboole_0(sK9)
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_1950,c_134])).

cnf(c_618,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_133,c_132])).

cnf(c_1957,plain,
    ( sK9 = sK5 ),
    inference(resolution,[status(thm)],[c_1950,c_618])).

cnf(c_2362,plain,
    ( X0 != sK5
    | sK9 = X0 ),
    inference(resolution,[status(thm)],[c_1957,c_133])).

cnf(c_2363,plain,
    ( sK9 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2362])).

cnf(c_3601,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK9)
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_3603,plain,
    ( v1_xboole_0(sK9)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK9 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3601])).

cnf(c_3846,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_3847,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3846])).

cnf(c_6900,plain,
    ( sK7 = X1
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2645,c_145,c_503,c_1735,c_1960,c_2363,c_3603,c_3847])).

cnf(c_6901,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK7 = X1 ),
    inference(renaming,[status(thm)],[c_6900])).

cnf(c_10,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1691,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(sK6,sK7) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_10])).

cnf(c_1693,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(sK6,sK7) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_10])).

cnf(c_1706,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k1_xboole_0
    | k2_zfmisc_1(sK6,sK7) = X0 ),
    inference(demodulation,[status(thm)],[c_1693,c_13])).

cnf(c_2077,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
    | k2_zfmisc_1(sK6,sK7) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1691,c_12,c_145,c_392,c_1706])).

cnf(c_2084,plain,
    ( k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK2,sK3) ),
    inference(equality_resolution,[status(thm)],[c_2077])).

cnf(c_6903,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK7 = X1 ),
    inference(light_normalisation,[status(thm)],[c_6901,c_1292,c_2084])).

cnf(c_6909,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK7 = sK3 ),
    inference(equality_resolution,[status(thm)],[c_6903])).

cnf(c_2648,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK6 = X0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2623,c_10])).

cnf(c_6914,plain,
    ( sK6 = X0
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2648,c_145,c_503,c_1735,c_1960,c_2363,c_3603,c_3847])).

cnf(c_6915,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK6 = X0 ),
    inference(renaming,[status(thm)],[c_6914])).

cnf(c_6917,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK6 = X0 ),
    inference(light_normalisation,[status(thm)],[c_6915,c_1292,c_2084])).

cnf(c_6923,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | sK6 = sK2 ),
    inference(equality_resolution,[status(thm)],[c_6917])).

cnf(c_7326,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2632,c_3954,c_6909,c_6923])).

cnf(c_7096,plain,
    ( v1_xboole_0(k2_zfmisc_1(X0,sK9))
    | ~ v1_xboole_0(k2_zfmisc_1(X1,sK5))
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_1871,c_1957])).

cnf(c_7098,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK9))
    | ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7096])).

cnf(c_457,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k2_zfmisc_1(X0,X1)
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_4553,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k2_zfmisc_1(X0,sK9)
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) != X0
    | sK5 != sK9 ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_4554,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k2_zfmisc_1(k1_xboole_0,sK9)
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) != k1_xboole_0
    | sK5 != sK9 ),
    inference(instantiation,[status(thm)],[c_4553])).

cnf(c_370,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5))
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13021,c_11287,c_7326,c_7098,c_4554,c_503,c_496,c_468,c_453,c_370,c_145,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.54/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/0.98  
% 3.54/0.98  ------  iProver source info
% 3.54/0.98  
% 3.54/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.54/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/0.98  git: non_committed_changes: false
% 3.54/0.98  git: last_make_outside_of_git: false
% 3.54/0.98  
% 3.54/0.98  ------ 
% 3.54/0.98  ------ Parsing...
% 3.54/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  ------ Proving...
% 3.54/0.98  ------ Problem Properties 
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  clauses                                 14
% 3.54/0.98  conjectures                             3
% 3.54/0.98  EPR                                     4
% 3.54/0.98  Horn                                    8
% 3.54/0.98  unary                                   3
% 3.54/0.98  binary                                  5
% 3.54/0.98  lits                                    32
% 3.54/0.98  lits eq                                 22
% 3.54/0.98  fd_pure                                 0
% 3.54/0.98  fd_pseudo                               0
% 3.54/0.98  fd_cond                                 1
% 3.54/0.98  fd_pseudo_cond                          3
% 3.54/0.98  AC symbols                              0
% 3.54/0.98  
% 3.54/0.98  ------ Input Options Time Limit: Unbounded
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ 
% 3.54/0.98  Current options:
% 3.54/0.98  ------ 
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  % SZS status Theorem for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  fof(f7,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f13,plain,(
% 3.54/0.98    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.54/0.98    inference(ennf_transformation,[],[f7])).
% 3.54/0.98  
% 3.54/0.98  fof(f34,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f13])).
% 3.54/0.98  
% 3.54/0.98  fof(f1,axiom,(
% 3.54/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f18,plain,(
% 3.54/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.54/0.98    inference(nnf_transformation,[],[f1])).
% 3.54/0.98  
% 3.54/0.98  fof(f19,plain,(
% 3.54/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.54/0.98    inference(rectify,[],[f18])).
% 3.54/0.98  
% 3.54/0.98  fof(f20,plain,(
% 3.54/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f21,plain,(
% 3.54/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.54/0.98  
% 3.54/0.98  fof(f27,plain,(
% 3.54/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f21])).
% 3.54/0.98  
% 3.54/0.98  fof(f26,plain,(
% 3.54/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f21])).
% 3.54/0.98  
% 3.54/0.98  fof(f8,axiom,(
% 3.54/0.98    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f14,plain,(
% 3.54/0.98    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 3.54/0.98    inference(ennf_transformation,[],[f8])).
% 3.54/0.98  
% 3.54/0.98  fof(f15,plain,(
% 3.54/0.98    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 3.54/0.98    inference(flattening,[],[f14])).
% 3.54/0.98  
% 3.54/0.98  fof(f38,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f15])).
% 3.54/0.98  
% 3.54/0.98  fof(f5,axiom,(
% 3.54/0.98    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f32,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f5])).
% 3.54/0.98  
% 3.54/0.98  fof(f43,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 3.54/0.98    inference(definition_unfolding,[],[f38,f32,f32,f32])).
% 3.54/0.98  
% 3.54/0.98  fof(f9,conjecture,(
% 3.54/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f10,negated_conjecture,(
% 3.54/0.98    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.54/0.98    inference(negated_conjecture,[],[f9])).
% 3.54/0.98  
% 3.54/0.98  fof(f16,plain,(
% 3.54/0.98    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 3.54/0.98    inference(ennf_transformation,[],[f10])).
% 3.54/0.98  
% 3.54/0.98  fof(f17,plain,(
% 3.54/0.98    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 3.54/0.98    inference(flattening,[],[f16])).
% 3.54/0.98  
% 3.54/0.98  fof(f24,plain,(
% 3.54/0.98    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK5 != sK9 | sK4 != sK8 | sK3 != sK7 | sK2 != sK6) & k1_xboole_0 != k4_zfmisc_1(sK2,sK3,sK4,sK5) & k4_zfmisc_1(sK2,sK3,sK4,sK5) = k4_zfmisc_1(sK6,sK7,sK8,sK9))),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f25,plain,(
% 3.54/0.98    (sK5 != sK9 | sK4 != sK8 | sK3 != sK7 | sK2 != sK6) & k1_xboole_0 != k4_zfmisc_1(sK2,sK3,sK4,sK5) & k4_zfmisc_1(sK2,sK3,sK4,sK5) = k4_zfmisc_1(sK6,sK7,sK8,sK9)),
% 3.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f17,f24])).
% 3.54/0.98  
% 3.54/0.98  fof(f39,plain,(
% 3.54/0.98    k4_zfmisc_1(sK2,sK3,sK4,sK5) = k4_zfmisc_1(sK6,sK7,sK8,sK9)),
% 3.54/0.98    inference(cnf_transformation,[],[f25])).
% 3.54/0.98  
% 3.54/0.98  fof(f6,axiom,(
% 3.54/0.98    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f33,plain,(
% 3.54/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f6])).
% 3.54/0.98  
% 3.54/0.98  fof(f42,plain,(
% 3.54/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.54/0.98    inference(definition_unfolding,[],[f33,f32])).
% 3.54/0.98  
% 3.54/0.98  fof(f47,plain,(
% 3.54/0.98    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)),
% 3.54/0.98    inference(definition_unfolding,[],[f39,f42,f42])).
% 3.54/0.98  
% 3.54/0.98  fof(f40,plain,(
% 3.54/0.98    k1_xboole_0 != k4_zfmisc_1(sK2,sK3,sK4,sK5)),
% 3.54/0.98    inference(cnf_transformation,[],[f25])).
% 3.54/0.98  
% 3.54/0.98  fof(f46,plain,(
% 3.54/0.98    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5)),
% 3.54/0.98    inference(definition_unfolding,[],[f40,f42])).
% 3.54/0.98  
% 3.54/0.98  fof(f2,axiom,(
% 3.54/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f11,plain,(
% 3.54/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f2])).
% 3.54/0.98  
% 3.54/0.98  fof(f28,plain,(
% 3.54/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f11])).
% 3.54/0.98  
% 3.54/0.98  fof(f4,axiom,(
% 3.54/0.98    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f12,plain,(
% 3.54/0.98    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.54/0.98    inference(ennf_transformation,[],[f4])).
% 3.54/0.98  
% 3.54/0.98  fof(f30,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.54/0.98    inference(cnf_transformation,[],[f12])).
% 3.54/0.98  
% 3.54/0.98  fof(f31,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.54/0.98    inference(cnf_transformation,[],[f12])).
% 3.54/0.98  
% 3.54/0.98  fof(f41,plain,(
% 3.54/0.98    sK5 != sK9 | sK4 != sK8 | sK3 != sK7 | sK2 != sK6),
% 3.54/0.98    inference(cnf_transformation,[],[f25])).
% 3.54/0.98  
% 3.54/0.98  fof(f37,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f15])).
% 3.54/0.98  
% 3.54/0.98  fof(f44,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 3.54/0.98    inference(definition_unfolding,[],[f37,f32,f32,f32])).
% 3.54/0.98  
% 3.54/0.98  fof(f3,axiom,(
% 3.54/0.98    ? [X0] : v1_xboole_0(X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f22,plain,(
% 3.54/0.98    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK1)),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f23,plain,(
% 3.54/0.98    v1_xboole_0(sK1)),
% 3.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f22])).
% 3.54/0.98  
% 3.54/0.98  fof(f29,plain,(
% 3.54/0.98    v1_xboole_0(sK1)),
% 3.54/0.98    inference(cnf_transformation,[],[f23])).
% 3.54/0.98  
% 3.54/0.98  fof(f35,plain,(
% 3.54/0.98    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f13])).
% 3.54/0.98  
% 3.54/0.98  fof(f36,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f15])).
% 3.54/0.98  
% 3.54/0.98  fof(f45,plain,(
% 3.54/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 3.54/0.98    inference(definition_unfolding,[],[f36,f32,f32,f32])).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7,plain,
% 3.54/0.98      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.54/0.98      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.54/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_0,plain,
% 3.54/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1339,plain,
% 3.54/0.98      ( r2_hidden(k1_mcart_1(sK0(k2_zfmisc_1(X0,X1))),X0)
% 3.54/0.98      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.54/0.98      inference(resolution,[status(thm)],[c_7,c_0]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1,plain,
% 3.54/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.54/0.98      inference(cnf_transformation,[],[f26]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3551,plain,
% 3.54/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.54/0.98      inference(resolution,[status(thm)],[c_1339,c_1]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_136,plain,
% 3.54/0.98      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.54/0.98      theory(equality) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_134,plain,
% 3.54/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.54/0.98      theory(equality) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1871,plain,
% 3.54/0.98      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
% 3.54/0.98      | v1_xboole_0(k2_zfmisc_1(X2,X3))
% 3.54/0.98      | X2 != X0
% 3.54/0.98      | X3 != X1 ),
% 3.54/0.98      inference(resolution,[status(thm)],[c_136,c_134]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8,plain,
% 3.54/0.98      ( X0 = X1
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = k1_xboole_0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_13,negated_conjecture,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) ),
% 3.54/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1946,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) = k1_xboole_0
% 3.54/0.98      | sK5 = sK9 ),
% 3.54/0.98      inference(resolution,[status(thm)],[c_8,c_13]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_12,negated_conjecture,
% 3.54/0.98      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) ),
% 3.54/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_132,plain,( X0 = X0 ),theory(equality) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_145,plain,
% 3.54/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_132]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_133,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_391,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != X0
% 3.54/0.98      | k1_xboole_0 != X0
% 3.54/0.98      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_133]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_453,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)
% 3.54/0.98      | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)
% 3.54/0.98      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_391]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_393,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK9) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK9)
% 3.54/0.98      | sK5 = sK9 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_468,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)
% 3.54/0.98      | sK5 = sK9 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_393]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_495,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) != X0
% 3.54/0.98      | k1_xboole_0 != X0
% 3.54/0.98      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_133]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_496,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) != k1_xboole_0
% 3.54/0.98      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9)
% 3.54/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_495]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1950,plain,
% 3.54/0.98      ( sK5 = sK9 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_1946,c_13,c_12,c_145,c_453,c_468,c_496]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_7068,plain,
% 3.54/0.98      ( ~ v1_xboole_0(k2_zfmisc_1(X0,sK9))
% 3.54/0.98      | v1_xboole_0(k2_zfmisc_1(X1,sK5))
% 3.54/0.98      | X1 != X0 ),
% 3.54/0.98      inference(resolution,[status(thm)],[c_1871,c_1950]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2,plain,
% 3.54/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_11737,plain,
% 3.54/0.98      ( ~ v1_xboole_0(X0)
% 3.54/0.98      | ~ v1_xboole_0(k2_zfmisc_1(X0,sK9))
% 3.54/0.98      | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5)) ),
% 3.54/0.98      inference(resolution,[status(thm)],[c_7068,c_2]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_13019,plain,
% 3.54/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5)) ),
% 3.54/0.98      inference(backward_subsumption_resolution,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_3551,c_11737]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_13021,plain,
% 3.54/0.98      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5))
% 3.54/0.98      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_13019]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_432,plain,
% 3.54/0.98      ( ~ v1_xboole_0(X0)
% 3.54/0.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5))
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != X0 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_134]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_11284,plain,
% 3.54/0.98      ( ~ v1_xboole_0(k2_zfmisc_1(X0,sK9))
% 3.54/0.98      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5))
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(X0,sK9) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_432]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_11287,plain,
% 3.54/0.98      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5))
% 3.54/0.98      | ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK9))
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k1_xboole_0,sK9) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_11284]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5,plain,
% 3.54/0.98      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 3.54/0.98      | k1_xboole_0 = X0
% 3.54/0.98      | k1_xboole_0 = X1 ),
% 3.54/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_679,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
% 3.54/0.98      | k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5)) = k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)
% 3.54/0.98      | sK9 = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_13,c_5]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1154,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.98      | sK9 = k1_xboole_0
% 3.54/0.98      | sK5 = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_5,c_679]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_446,plain,
% 3.54/0.98      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_133]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_636,plain,
% 3.54/0.98      ( X0 != sK9 | sK5 = X0 | sK5 != sK9 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_446]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_637,plain,
% 3.54/0.98      ( sK5 != sK9 | sK5 = k1_xboole_0 | k1_xboole_0 != sK9 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_636]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1142,plain,
% 3.54/0.98      ( X0 != X1 | X0 = sK9 | sK9 != X1 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_133]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1143,plain,
% 3.54/0.98      ( sK9 != k1_xboole_0
% 3.54/0.98      | k1_xboole_0 = sK9
% 3.54/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_1142]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2622,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 3.54/0.98      | sK5 = k1_xboole_0 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_1154,c_13,c_12,c_145,c_453,c_468,c_496,c_637,c_1143]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2623,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.98      | sK5 = k1_xboole_0 ),
% 3.54/0.98      inference(renaming,[status(thm)],[c_2622]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4,plain,
% 3.54/0.98      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 3.54/0.98      | k1_xboole_0 = X0
% 3.54/0.98      | k1_xboole_0 = X1 ),
% 3.54/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2632,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(sK6,sK7) = k1_xboole_0
% 3.54/0.98      | k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = sK8
% 3.54/0.98      | sK8 = k1_xboole_0
% 3.54/0.98      | sK5 = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2623,c_4]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_826,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.98      | sK9 = X2 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_13,c_8]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_392,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k1_xboole_0
% 3.54/0.98      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5)
% 3.54/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_391]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_828,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.98      | sK9 = X2 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_13,c_8]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_841,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k1_xboole_0
% 3.54/0.98      | sK9 = X2 ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_828,c_13]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1156,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.98      | sK9 = X2 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_826,c_12,c_145,c_392,c_841]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1163,plain,
% 3.54/0.98      ( sK9 = sK5 ),
% 3.54/0.98      inference(equality_resolution,[status(thm)],[c_1156]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_11,negated_conjecture,
% 3.54/0.98      ( sK2 != sK6 | sK3 != sK7 | sK4 != sK8 | sK5 != sK9 ),
% 3.54/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3445,plain,
% 3.54/0.98      ( sK6 != sK2 | sK7 != sK3 | sK8 != sK4 | sK5 != sK5 ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_1163,c_11]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3449,plain,
% 3.54/0.98      ( sK6 != sK2 | sK7 != sK3 | sK8 != sK4 ),
% 3.54/0.98      inference(equality_resolution_simp,[status(thm)],[c_3445]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9,plain,
% 3.54/0.98      ( X0 = X1
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = k1_xboole_0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_862,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.98      | sK8 = X1 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_13,c_9]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_864,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.98      | sK8 = X1 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_13,c_9]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_877,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k1_xboole_0
% 3.54/0.98      | sK8 = X1 ),
% 3.54/0.98      inference(demodulation,[status(thm)],[c_864,c_13]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1285,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.98      | sK8 = X1 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_862,c_12,c_145,c_392,c_877]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1292,plain,
% 3.54/0.98      ( sK8 = sK4 ),
% 3.54/0.98      inference(equality_resolution,[status(thm)],[c_1285]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3953,plain,
% 3.54/0.98      ( sK7 != sK3 | sK6 != sK2 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_3449,c_1292]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3954,plain,
% 3.54/0.98      ( sK6 != sK2 | sK7 != sK3 ),
% 3.54/0.98      inference(renaming,[status(thm)],[c_3953]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2645,plain,
% 3.54/0.98      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
% 3.54/0.98      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.98      | sK7 = X1
% 3.54/0.98      | sK5 = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2623,c_9]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3,plain,
% 3.54/0.98      ( v1_xboole_0(sK1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_276,plain,
% 3.54/0.99      ( v1_xboole_0(sK1) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_277,plain,
% 3.54/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_500,plain,
% 3.54/0.99      ( sK1 = k1_xboole_0 ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_276,c_277]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_502,plain,
% 3.54/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_500,c_276]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_503,plain,
% 3.54/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.54/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_502]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_902,plain,
% 3.54/0.99      ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5)) ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6,plain,
% 3.54/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.54/0.99      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.54/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_913,plain,
% 3.54/0.99      ( r2_hidden(k2_mcart_1(sK0(k2_zfmisc_1(X0,X1))),X1)
% 3.54/0.99      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_6,c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1522,plain,
% 3.54/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_913,c_1]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1735,plain,
% 3.54/0.99      ( ~ v1_xboole_0(sK5) ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_902,c_1522]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1960,plain,
% 3.54/0.99      ( ~ v1_xboole_0(sK9) | v1_xboole_0(sK5) ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_1950,c_134]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_618,plain,
% 3.54/0.99      ( X0 != X1 | X1 = X0 ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_133,c_132]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1957,plain,
% 3.54/0.99      ( sK9 = sK5 ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_1950,c_618]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2362,plain,
% 3.54/0.99      ( X0 != sK5 | sK9 = X0 ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_1957,c_133]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2363,plain,
% 3.54/0.99      ( sK9 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_2362]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3601,plain,
% 3.54/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK9) | sK9 != X0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_134]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3603,plain,
% 3.54/0.99      ( v1_xboole_0(sK9)
% 3.54/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.54/0.99      | sK9 != k1_xboole_0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_3601]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3846,plain,
% 3.54/0.99      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_133]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3847,plain,
% 3.54/0.99      ( sK5 != k1_xboole_0
% 3.54/0.99      | k1_xboole_0 = sK5
% 3.54/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_3846]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6900,plain,
% 3.54/0.99      ( sK7 = X1
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_2645,c_145,c_503,c_1735,c_1960,c_2363,c_3603,c_3847]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6901,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.99      | sK7 = X1 ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_6900]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_10,plain,
% 3.54/0.99      ( X0 = X1
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5) = k1_xboole_0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1691,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k1_xboole_0
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.99      | k2_zfmisc_1(sK6,sK7) = X0 ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_13,c_10]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1693,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8),sK9) = k1_xboole_0
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.99      | k2_zfmisc_1(sK6,sK7) = X0 ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_13,c_10]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1706,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k1_xboole_0
% 3.54/0.99      | k2_zfmisc_1(sK6,sK7) = X0 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_1693,c_13]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2077,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
% 3.54/0.99      | k2_zfmisc_1(sK6,sK7) = X0 ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_1691,c_12,c_145,c_392,c_1706]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2084,plain,
% 3.54/0.99      ( k2_zfmisc_1(sK6,sK7) = k2_zfmisc_1(sK2,sK3) ),
% 3.54/0.99      inference(equality_resolution,[status(thm)],[c_2077]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6903,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.99      | sK7 = X1 ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_6901,c_1292,c_2084]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6909,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 | sK7 = sK3 ),
% 3.54/0.99      inference(equality_resolution,[status(thm)],[c_6903]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2648,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.99      | sK6 = X0
% 3.54/0.99      | sK5 = k1_xboole_0 ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_2623,c_10]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6914,plain,
% 3.54/0.99      ( sK6 = X0
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_2648,c_145,c_503,c_1735,c_1960,c_2363,c_3603,c_3847]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6915,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.99      | sK6 = X0 ),
% 3.54/0.99      inference(renaming,[status(thm)],[c_6914]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6917,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.54/0.99      | sK6 = X0 ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_6915,c_1292,c_2084]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_6923,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 | sK6 = sK2 ),
% 3.54/0.99      inference(equality_resolution,[status(thm)],[c_6917]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7326,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
% 3.54/0.99      inference(global_propositional_subsumption,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_2632,c_3954,c_6909,c_6923]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7096,plain,
% 3.54/0.99      ( v1_xboole_0(k2_zfmisc_1(X0,sK9))
% 3.54/0.99      | ~ v1_xboole_0(k2_zfmisc_1(X1,sK5))
% 3.54/0.99      | X0 != X1 ),
% 3.54/0.99      inference(resolution,[status(thm)],[c_1871,c_1957]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7098,plain,
% 3.54/0.99      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK9))
% 3.54/0.99      | ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5))
% 3.54/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_7096]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_457,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k2_zfmisc_1(X0,X1)
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) != X0
% 3.54/0.99      | sK5 != X1 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_136]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4553,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k2_zfmisc_1(X0,sK9)
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) != X0
% 3.54/0.99      | sK5 != sK9 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_457]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4554,plain,
% 3.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) = k2_zfmisc_1(k1_xboole_0,sK9)
% 3.54/0.99      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) != k1_xboole_0
% 3.54/0.99      | sK5 != sK9 ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_4553]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_370,plain,
% 3.54/0.99      ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5))
% 3.54/0.99      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4),sK5) ),
% 3.54/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(contradiction,plain,
% 3.54/0.99      ( $false ),
% 3.54/0.99      inference(minisat,
% 3.54/0.99                [status(thm)],
% 3.54/0.99                [c_13021,c_11287,c_7326,c_7098,c_4554,c_503,c_496,c_468,
% 3.54/0.99                 c_453,c_370,c_145,c_12,c_13]) ).
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  ------                               Statistics
% 3.54/0.99  
% 3.54/0.99  ------ Selected
% 3.54/0.99  
% 3.54/0.99  total_time:                             0.441
% 3.54/0.99  
%------------------------------------------------------------------------------
