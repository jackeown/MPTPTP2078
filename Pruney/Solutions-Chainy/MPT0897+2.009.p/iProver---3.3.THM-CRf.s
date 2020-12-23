%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:42 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 561 expanded)
%              Number of clauses        :   39 (  99 expanded)
%              Number of leaves         :    9 ( 159 expanded)
%              Depth                    :   17
%              Number of atoms          :  237 (1716 expanded)
%              Number of equality atoms :  236 (1715 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f11])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f15])).

fof(f29,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f42,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f29,f32,f32])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f9])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f22,f19,f19,f19])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f21,f19,f19,f19])).

fof(f30,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f24,f32])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f25,f32])).

fof(f46,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f39])).

fof(f31,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X2 = X5
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) ) ),
    inference(definition_unfolding,[],[f23,f19,f19,f19])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f44,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f37])).

cnf(c_1,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_12,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_584,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_809,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_584])).

cnf(c_3,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_25,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_709,plain,
    ( X0 != X1
    | X2 = X3
    | k2_zfmisc_1(X4,X2) != k2_zfmisc_1(X5,X3)
    | k2_zfmisc_1(k2_zfmisc_1(X5,X3),X1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3,c_25])).

cnf(c_4,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)
    | k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2262,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    inference(resolution,[status(thm)],[c_4,c_12])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_24,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_122,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_168,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
    | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(c_184,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_185,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_3187,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2262,c_12,c_11,c_13,c_14,c_168,c_185])).

cnf(c_12670,plain,
    ( X0 != X1
    | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),X1) = k1_xboole_0
    | sK1 = sK5 ),
    inference(resolution,[status(thm)],[c_709,c_3187])).

cnf(c_10,negated_conjecture,
    ( sK0 != sK4
    | sK1 != sK5
    | sK2 != sK6
    | sK3 != sK7 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2,plain,
    ( X0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
    | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_125,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK7) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X2,X3),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK7)
    | sK3 = sK7 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_196,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
    | sK3 = sK7 ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_707,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
    | sK2 = sK6 ),
    inference(resolution,[status(thm)],[c_3,c_12])).

cnf(c_2264,plain,
    ( X0 != X1
    | X2 = X3
    | k2_zfmisc_1(X2,X4) != k2_zfmisc_1(X3,X5)
    | k2_zfmisc_1(k2_zfmisc_1(X3,X5),X1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_25])).

cnf(c_12693,plain,
    ( X0 != X1
    | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),X1) = k1_xboole_0
    | sK0 = sK4 ),
    inference(resolution,[status(thm)],[c_2264,c_3187])).

cnf(c_13231,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),X1) = k1_xboole_0
    | X0 != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12670,c_12,c_11,c_10,c_13,c_14,c_168,c_185,c_196,c_707,c_12693])).

cnf(c_13232,plain,
    ( X0 != X1
    | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),X1) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_13231])).

cnf(c_816,plain,
    ( sK2 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_12,c_11,c_13,c_14,c_168,c_185])).

cnf(c_13249,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_13232,c_816])).

cnf(c_13961,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_809,c_13249])).

cnf(c_13967,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) ),
    inference(demodulation,[status(thm)],[c_13961,c_12])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_309,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_13969,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13967,c_309])).

cnf(c_123,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_122])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13969,c_123,c_14,c_13,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:36:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.44/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/1.00  
% 3.44/1.00  ------  iProver source info
% 3.44/1.00  
% 3.44/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.44/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/1.00  git: non_committed_changes: false
% 3.44/1.00  git: last_make_outside_of_git: false
% 3.44/1.00  
% 3.44/1.00  ------ 
% 3.44/1.00  ------ Parsing...
% 3.44/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/1.00  
% 3.44/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.44/1.00  ------ Proving...
% 3.44/1.00  ------ Problem Properties 
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  clauses                                 13
% 3.44/1.00  conjectures                             3
% 3.44/1.00  EPR                                     1
% 3.44/1.00  Horn                                    7
% 3.44/1.00  unary                                   6
% 3.44/1.00  binary                                  0
% 3.44/1.00  lits                                    30
% 3.44/1.00  lits eq                                 30
% 3.44/1.00  fd_pure                                 0
% 3.44/1.00  fd_pseudo                               0
% 3.44/1.00  fd_cond                                 1
% 3.44/1.00  fd_pseudo_cond                          3
% 3.44/1.00  AC symbols                              0
% 3.44/1.00  
% 3.44/1.00  ------ Input Options Time Limit: Unbounded
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  ------ 
% 3.44/1.00  Current options:
% 3.44/1.00  ------ 
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  ------ Proving...
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  % SZS status Theorem for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  fof(f1,axiom,(
% 3.44/1.00    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f8,plain,(
% 3.44/1.00    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.44/1.00    inference(ennf_transformation,[],[f1])).
% 3.44/1.00  
% 3.44/1.00  fof(f17,plain,(
% 3.44/1.00    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.44/1.00    inference(cnf_transformation,[],[f8])).
% 3.44/1.00  
% 3.44/1.00  fof(f6,conjecture,(
% 3.44/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f7,negated_conjecture,(
% 3.44/1.00    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.44/1.00    inference(negated_conjecture,[],[f6])).
% 3.44/1.00  
% 3.44/1.00  fof(f11,plain,(
% 3.44/1.00    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 3.44/1.00    inference(ennf_transformation,[],[f7])).
% 3.44/1.00  
% 3.44/1.00  fof(f12,plain,(
% 3.44/1.00    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 3.44/1.00    inference(flattening,[],[f11])).
% 3.44/1.00  
% 3.44/1.00  fof(f15,plain,(
% 3.44/1.00    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 3.44/1.00    introduced(choice_axiom,[])).
% 3.44/1.00  
% 3.44/1.00  fof(f16,plain,(
% 3.44/1.00    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 3.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f15])).
% 3.44/1.00  
% 3.44/1.00  fof(f29,plain,(
% 3.44/1.00    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 3.44/1.00    inference(cnf_transformation,[],[f16])).
% 3.44/1.00  
% 3.44/1.00  fof(f3,axiom,(
% 3.44/1.00    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f20,plain,(
% 3.44/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f3])).
% 3.44/1.00  
% 3.44/1.00  fof(f2,axiom,(
% 3.44/1.00    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f19,plain,(
% 3.44/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f2])).
% 3.44/1.00  
% 3.44/1.00  fof(f32,plain,(
% 3.44/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.44/1.00    inference(definition_unfolding,[],[f20,f19])).
% 3.44/1.00  
% 3.44/1.00  fof(f42,plain,(
% 3.44/1.00    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 3.44/1.00    inference(definition_unfolding,[],[f29,f32,f32])).
% 3.44/1.00  
% 3.44/1.00  fof(f4,axiom,(
% 3.44/1.00    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f9,plain,(
% 3.44/1.00    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 3.44/1.00    inference(ennf_transformation,[],[f4])).
% 3.44/1.00  
% 3.44/1.00  fof(f10,plain,(
% 3.44/1.00    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 3.44/1.00    inference(flattening,[],[f9])).
% 3.44/1.00  
% 3.44/1.00  fof(f22,plain,(
% 3.44/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f10])).
% 3.44/1.00  
% 3.44/1.00  fof(f34,plain,(
% 3.44/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 3.44/1.00    inference(definition_unfolding,[],[f22,f19,f19,f19])).
% 3.44/1.00  
% 3.44/1.00  fof(f21,plain,(
% 3.44/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f10])).
% 3.44/1.00  
% 3.44/1.00  fof(f35,plain,(
% 3.44/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 3.44/1.00    inference(definition_unfolding,[],[f21,f19,f19,f19])).
% 3.44/1.00  
% 3.44/1.00  fof(f30,plain,(
% 3.44/1.00    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 3.44/1.00    inference(cnf_transformation,[],[f16])).
% 3.44/1.00  
% 3.44/1.00  fof(f41,plain,(
% 3.44/1.00    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 3.44/1.00    inference(definition_unfolding,[],[f30,f32])).
% 3.44/1.00  
% 3.44/1.00  fof(f5,axiom,(
% 3.44/1.00    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 3.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.44/1.00  
% 3.44/1.00  fof(f13,plain,(
% 3.44/1.00    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.44/1.00    inference(nnf_transformation,[],[f5])).
% 3.44/1.00  
% 3.44/1.00  fof(f14,plain,(
% 3.44/1.00    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.44/1.00    inference(flattening,[],[f13])).
% 3.44/1.00  
% 3.44/1.00  fof(f24,plain,(
% 3.44/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.44/1.00    inference(cnf_transformation,[],[f14])).
% 3.44/1.00  
% 3.44/1.00  fof(f40,plain,(
% 3.44/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.44/1.00    inference(definition_unfolding,[],[f24,f32])).
% 3.44/1.00  
% 3.44/1.00  fof(f25,plain,(
% 3.44/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f14])).
% 3.44/1.00  
% 3.44/1.00  fof(f39,plain,(
% 3.44/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.44/1.00    inference(definition_unfolding,[],[f25,f32])).
% 3.44/1.00  
% 3.44/1.00  fof(f46,plain,(
% 3.44/1.00    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 3.44/1.00    inference(equality_resolution,[],[f39])).
% 3.44/1.00  
% 3.44/1.00  fof(f31,plain,(
% 3.44/1.00    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 3.44/1.00    inference(cnf_transformation,[],[f16])).
% 3.44/1.00  
% 3.44/1.00  fof(f23,plain,(
% 3.44/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f10])).
% 3.44/1.00  
% 3.44/1.00  fof(f33,plain,(
% 3.44/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (X2 = X5 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) )),
% 3.44/1.00    inference(definition_unfolding,[],[f23,f19,f19,f19])).
% 3.44/1.00  
% 3.44/1.00  fof(f27,plain,(
% 3.44/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.44/1.00    inference(cnf_transformation,[],[f14])).
% 3.44/1.00  
% 3.44/1.00  fof(f37,plain,(
% 3.44/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.44/1.00    inference(definition_unfolding,[],[f27,f32])).
% 3.44/1.00  
% 3.44/1.00  fof(f44,plain,(
% 3.44/1.00    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 3.44/1.00    inference(equality_resolution,[],[f37])).
% 3.44/1.00  
% 3.44/1.00  cnf(c_1,plain,
% 3.44/1.00      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 3.44/1.00      | k1_xboole_0 = X1
% 3.44/1.00      | k1_xboole_0 = X0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f17]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_12,negated_conjecture,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
% 3.44/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_584,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 3.44/1.00      | k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
% 3.44/1.00      | sK7 = k1_xboole_0 ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_809,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.44/1.00      | sK7 = k1_xboole_0
% 3.44/1.00      | sK3 = k1_xboole_0 ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_1,c_584]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3,plain,
% 3.44/1.00      ( X0 = X1
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3) != k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5) = k1_xboole_0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_25,plain,
% 3.44/1.00      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.44/1.00      theory(equality) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_709,plain,
% 3.44/1.00      ( X0 != X1
% 3.44/1.00      | X2 = X3
% 3.44/1.00      | k2_zfmisc_1(X4,X2) != k2_zfmisc_1(X5,X3)
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(X5,X3),X1) = k1_xboole_0 ),
% 3.44/1.00      inference(resolution,[status(thm)],[c_3,c_25]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_4,plain,
% 3.44/1.00      ( X0 = X1
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5) = k1_xboole_0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2262,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
% 3.44/1.00      | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
% 3.44/1.00      inference(resolution,[status(thm)],[c_4,c_12]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_11,negated_conjecture,
% 3.44/1.00      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
% 3.44/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_9,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 3.44/1.00      | k1_xboole_0 = X1
% 3.44/1.00      | k1_xboole_0 = X0
% 3.44/1.00      | k1_xboole_0 = X3
% 3.44/1.00      | k1_xboole_0 = X2 ),
% 3.44/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_13,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 3.44/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_8,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_14,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_24,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_122,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != X0
% 3.44/1.00      | k1_xboole_0 != X0
% 3.44/1.00      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_168,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
% 3.44/1.00      | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
% 3.44/1.00      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_122]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_184,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) != X0
% 3.44/1.00      | k1_xboole_0 != X0
% 3.44/1.00      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_185,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) != k1_xboole_0
% 3.44/1.00      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
% 3.44/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_184]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_3187,plain,
% 3.44/1.00      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_2262,c_12,c_11,c_13,c_14,c_168,c_185]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_12670,plain,
% 3.44/1.00      ( X0 != X1
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),X1) = k1_xboole_0
% 3.44/1.00      | sK1 = sK5 ),
% 3.44/1.00      inference(resolution,[status(thm)],[c_709,c_3187]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_10,negated_conjecture,
% 3.44/1.00      ( sK0 != sK4 | sK1 != sK5 | sK2 != sK6 | sK3 != sK7 ),
% 3.44/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2,plain,
% 3.44/1.00      ( X0 = X1
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0) != k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1) = k1_xboole_0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_125,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK7) = k1_xboole_0
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(X2,X3),sK3) != k2_zfmisc_1(k2_zfmisc_1(X0,X1),sK7)
% 3.44/1.00      | sK3 = sK7 ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_196,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)
% 3.44/1.00      | sK3 = sK7 ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_125]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_707,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) = k1_xboole_0
% 3.44/1.00      | sK2 = sK6 ),
% 3.44/1.00      inference(resolution,[status(thm)],[c_3,c_12]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_2264,plain,
% 3.44/1.00      ( X0 != X1
% 3.44/1.00      | X2 = X3
% 3.44/1.00      | k2_zfmisc_1(X2,X4) != k2_zfmisc_1(X3,X5)
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(X3,X5),X1) = k1_xboole_0 ),
% 3.44/1.00      inference(resolution,[status(thm)],[c_4,c_25]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_12693,plain,
% 3.44/1.00      ( X0 != X1
% 3.44/1.00      | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),X1) = k1_xboole_0
% 3.44/1.00      | sK0 = sK4 ),
% 3.44/1.00      inference(resolution,[status(thm)],[c_2264,c_3187]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_13231,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),X1) = k1_xboole_0 | X0 != X1 ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_12670,c_12,c_11,c_10,c_13,c_14,c_168,c_185,c_196,
% 3.44/1.00                 c_707,c_12693]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_13232,plain,
% 3.44/1.00      ( X0 != X1 | k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),X1) = k1_xboole_0 ),
% 3.44/1.00      inference(renaming,[status(thm)],[c_13231]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_816,plain,
% 3.44/1.00      ( sK2 = sK6 ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_707,c_12,c_11,c_13,c_14,c_168,c_185]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_13249,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0 ),
% 3.44/1.00      inference(resolution,[status(thm)],[c_13232,c_816]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_13961,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) = k1_xboole_0 ),
% 3.44/1.00      inference(global_propositional_subsumption,
% 3.44/1.00                [status(thm)],
% 3.44/1.00                [c_809,c_13249]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_13967,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k1_xboole_0,sK7) ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_13961,c_12]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_6,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
% 3.44/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_309,plain,
% 3.44/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.44/1.00      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_13969,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0 ),
% 3.44/1.00      inference(demodulation,[status(thm)],[c_13967,c_309]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(c_123,plain,
% 3.44/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0
% 3.44/1.00      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
% 3.44/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.44/1.00      inference(instantiation,[status(thm)],[c_122]) ).
% 3.44/1.00  
% 3.44/1.00  cnf(contradiction,plain,
% 3.44/1.00      ( $false ),
% 3.44/1.00      inference(minisat,[status(thm)],[c_13969,c_123,c_14,c_13,c_11]) ).
% 3.44/1.00  
% 3.44/1.00  
% 3.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/1.00  
% 3.44/1.00  ------                               Statistics
% 3.44/1.00  
% 3.44/1.00  ------ Selected
% 3.44/1.00  
% 3.44/1.00  total_time:                             0.372
% 3.44/1.00  
%------------------------------------------------------------------------------
