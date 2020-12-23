%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0876+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:19 EST 2020

% Result     : Theorem 0.97s
% Output     : CNFRefutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 349 expanded)
%              Number of clauses        :   45 ( 110 expanded)
%              Number of leaves         :    7 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  223 (1663 expanded)
%              Number of equality atoms :  222 (1662 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f8])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f12])).

fof(f20,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f20,f14,f14])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f6])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f16])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_9,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( X0 = X1
    | k2_zfmisc_1(X0,X2) != k2_zfmisc_1(X1,X3)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_299,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k2_zfmisc_1(X0,X1)
    | k2_zfmisc_1(sK3,sK4) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_9,c_4])).

cnf(c_385,plain,
    ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_299])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_6,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_17,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_66,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_67,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_62,plain,
    ( k2_zfmisc_1(X0,sK1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_88,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_617,plain,
    ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_8,c_7,c_6,c_11,c_12,c_67,c_88])).

cnf(c_629,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | sK3 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_617,c_4])).

cnf(c_70,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_78,plain,
    ( X0 = X1
    | k2_zfmisc_1(X0,X2) != k2_zfmisc_1(X1,sK1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_125,plain,
    ( X0 = sK0
    | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_78])).

cnf(c_3,plain,
    ( X0 = X1
    | k2_zfmisc_1(X2,X0) != k2_zfmisc_1(X3,X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_76,plain,
    ( X0 = sK0
    | k2_zfmisc_1(X1,X0) != k2_zfmisc_1(X2,sK0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_114,plain,
    ( X0 = sK0
    | k2_zfmisc_1(X1,X0) != k2_zfmisc_1(sK2,sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_183,plain,
    ( k2_zfmisc_1(sK2,sK0) != k2_zfmisc_1(sK2,sK0)
    | sK0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_16,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_184,plain,
    ( k2_zfmisc_1(sK2,sK0) = k2_zfmisc_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_101,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_338,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_947,plain,
    ( k1_xboole_0 = X1
    | sK3 = X0
    | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_8,c_7,c_6,c_70,c_125,c_183,c_184,c_338])).

cnf(c_948,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | sK3 = X0
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_947])).

cnf(c_955,plain,
    ( sK3 = sK0
    | sK1 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_948])).

cnf(c_627,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | sK4 = X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_617,c_3])).

cnf(c_852,plain,
    ( k1_xboole_0 = X1
    | sK4 = X1
    | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_627,c_8,c_7,c_6,c_70,c_125,c_183,c_184,c_338])).

cnf(c_853,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | sK4 = X1
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_852])).

cnf(c_860,plain,
    ( sK4 = sK1
    | sK1 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_853])).

cnf(c_224,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != k2_zfmisc_1(X0,X1)
    | sK5 = X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_9,c_3])).

cnf(c_331,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | sK5 = sK2
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_224])).

cnf(c_430,plain,
    ( sK5 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_8,c_7,c_6,c_11,c_12,c_67,c_88])).

cnf(c_5,negated_conjecture,
    ( sK0 != sK3
    | sK1 != sK4
    | sK2 != sK5 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_437,plain,
    ( sK3 != sK0
    | sK4 != sK1
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_430,c_5])).

cnf(c_441,plain,
    ( sK3 != sK0
    | sK4 != sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_437])).

cnf(c_68,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_69,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_955,c_860,c_441,c_69,c_12,c_11,c_7])).


%------------------------------------------------------------------------------
