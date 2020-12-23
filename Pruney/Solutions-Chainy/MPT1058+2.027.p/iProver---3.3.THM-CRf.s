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
% DateTime   : Thu Dec  3 12:09:16 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 344 expanded)
%              Number of clauses        :   66 ( 122 expanded)
%              Number of leaves         :   18 (  85 expanded)
%              Depth                    :   19
%              Number of atoms          :  228 ( 738 expanded)
%              Number of equality atoms :  108 ( 340 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK3) != k10_relat_1(k7_relat_1(X0,sK2),sK3)
        & r1_tarski(k10_relat_1(X0,sK3),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK1,X2) != k10_relat_1(k7_relat_1(sK1,X1),X2)
          & r1_tarski(k10_relat_1(sK1,X2),X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k10_relat_1(sK1,sK3) != k10_relat_1(k7_relat_1(sK1,sK2),sK3)
    & r1_tarski(k10_relat_1(sK1,sK3),sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f28,f27])).

fof(f47,plain,(
    r1_tarski(k10_relat_1(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f44,f41])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f41,f42])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f41,f41])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    k10_relat_1(sK1,sK3) != k10_relat_1(k7_relat_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_578,plain,
    ( r1_tarski(k10_relat_1(sK1,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_582,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_584,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1742,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_582,c_584])).

cnf(c_5410,plain,
    ( k4_xboole_0(k4_xboole_0(k10_relat_1(sK1,sK3),X0),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_578,c_1742])).

cnf(c_6107,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(sK1,sK3),X0),X1) != iProver_top
    | r1_tarski(k1_xboole_0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5410,c_582])).

cnf(c_258,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_255,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1950,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_258,c_255])).

cnf(c_256,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1803,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_256,c_255])).

cnf(c_2268,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_1803,c_7])).

cnf(c_2448,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2)
    | r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[status(thm)],[c_1950,c_2268])).

cnf(c_10,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2647,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_2448,c_10])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2882,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_2647,c_6])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_722,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,sK0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_13,c_2])).

cnf(c_779,plain,
    ( ~ r1_tarski(X0,sK0(k4_xboole_0(X0,X1),X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_722,c_9])).

cnf(c_3095,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(resolution,[status(thm)],[c_2882,c_779])).

cnf(c_3096,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3095])).

cnf(c_1263,plain,
    ( k4_xboole_0(k10_relat_1(sK1,sK3),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_578,c_584])).

cnf(c_1739,plain,
    ( r1_tarski(k10_relat_1(sK1,sK3),X0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_582])).

cnf(c_2254,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_1739])).

cnf(c_5421,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2254,c_1742])).

cnf(c_6255,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) != iProver_top
    | r1_tarski(k1_xboole_0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5421,c_582])).

cnf(c_7974,plain,
    ( r1_tarski(k1_xboole_0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6107,c_3096,c_6255])).

cnf(c_7975,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7974])).

cnf(c_7979,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7975,c_584])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_577,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_580,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_634,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_580,c_11])).

cnf(c_4422,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_577,c_634])).

cnf(c_581,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1283,plain,
    ( r1_tarski(k1_xboole_0,k10_relat_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_581])).

cnf(c_1447,plain,
    ( k4_xboole_0(k1_xboole_0,k10_relat_1(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1283,c_584])).

cnf(c_1727,plain,
    ( k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k10_relat_1(sK1,sK3))) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1447,c_11])).

cnf(c_4526,plain,
    ( k10_relat_1(k7_relat_1(sK1,k1_xboole_0),sK3) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4422,c_1727])).

cnf(c_12042,plain,
    ( k10_relat_1(k7_relat_1(sK1,k1_xboole_0),sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7979,c_4526])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_583,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1194,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X1,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_583])).

cnf(c_1197,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) != k1_xboole_0
    | r1_tarski(X1,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1194,c_11])).

cnf(c_4515,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),X1) != k1_xboole_0
    | r1_tarski(k10_relat_1(sK1,X1),k4_xboole_0(k10_relat_1(sK1,X1),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4422,c_1197])).

cnf(c_12126,plain,
    ( r1_tarski(k10_relat_1(sK1,sK3),k4_xboole_0(k10_relat_1(sK1,sK3),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12042,c_4515])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_586,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2745,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,k4_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_582,c_586])).

cnf(c_17895,plain,
    ( k4_xboole_0(k10_relat_1(sK1,sK3),k1_xboole_0) = k10_relat_1(sK1,sK3)
    | r1_tarski(k10_relat_1(sK1,sK3),k10_relat_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12126,c_2745])).

cnf(c_895,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_1284,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,k10_relat_1(sK1,sK3))) = k4_xboole_0(k10_relat_1(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1263,c_895])).

cnf(c_4525,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK2),sK3) = k4_xboole_0(k10_relat_1(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4422,c_1284])).

cnf(c_14,negated_conjecture,
    ( k10_relat_1(sK1,sK3) != k10_relat_1(k7_relat_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_5069,plain,
    ( k4_xboole_0(k10_relat_1(sK1,sK3),k1_xboole_0) != k10_relat_1(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_4525,c_14])).

cnf(c_1520,plain,
    ( r1_tarski(k10_relat_1(sK1,sK3),k10_relat_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1523,plain,
    ( r1_tarski(k10_relat_1(sK1,sK3),k10_relat_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17895,c_5069,c_1523])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.41/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/1.49  
% 7.41/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.41/1.49  
% 7.41/1.49  ------  iProver source info
% 7.41/1.49  
% 7.41/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.41/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.41/1.49  git: non_committed_changes: false
% 7.41/1.49  git: last_make_outside_of_git: false
% 7.41/1.49  
% 7.41/1.49  ------ 
% 7.41/1.49  ------ Parsing...
% 7.41/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.41/1.49  
% 7.41/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.41/1.49  
% 7.41/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.41/1.49  
% 7.41/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.41/1.49  ------ Proving...
% 7.41/1.49  ------ Problem Properties 
% 7.41/1.49  
% 7.41/1.49  
% 7.41/1.49  clauses                                 16
% 7.41/1.49  conjectures                             3
% 7.41/1.49  EPR                                     5
% 7.41/1.49  Horn                                    15
% 7.41/1.49  unary                                   7
% 7.41/1.49  binary                                  7
% 7.41/1.49  lits                                    27
% 7.41/1.49  lits eq                                 7
% 7.41/1.49  fd_pure                                 0
% 7.41/1.49  fd_pseudo                               0
% 7.41/1.49  fd_cond                                 0
% 7.41/1.49  fd_pseudo_cond                          1
% 7.41/1.49  AC symbols                              0
% 7.41/1.49  
% 7.41/1.49  ------ Input Options Time Limit: Unbounded
% 7.41/1.49  
% 7.41/1.49  
% 7.41/1.49  ------ 
% 7.41/1.49  Current options:
% 7.41/1.49  ------ 
% 7.41/1.49  
% 7.41/1.49  
% 7.41/1.49  
% 7.41/1.49  
% 7.41/1.49  ------ Proving...
% 7.41/1.49  
% 7.41/1.49  
% 7.41/1.49  % SZS status Theorem for theBenchmark.p
% 7.41/1.49  
% 7.41/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.41/1.49  
% 7.41/1.49  fof(f12,conjecture,(
% 7.41/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f13,negated_conjecture,(
% 7.41/1.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.41/1.49    inference(negated_conjecture,[],[f12])).
% 7.41/1.49  
% 7.41/1.49  fof(f14,plain,(
% 7.41/1.49    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.41/1.49    inference(pure_predicate_removal,[],[f13])).
% 7.41/1.49  
% 7.41/1.49  fof(f19,plain,(
% 7.41/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0))),
% 7.41/1.49    inference(ennf_transformation,[],[f14])).
% 7.41/1.49  
% 7.41/1.49  fof(f28,plain,(
% 7.41/1.49    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK3) != k10_relat_1(k7_relat_1(X0,sK2),sK3) & r1_tarski(k10_relat_1(X0,sK3),sK2))) )),
% 7.41/1.49    introduced(choice_axiom,[])).
% 7.41/1.49  
% 7.41/1.49  fof(f27,plain,(
% 7.41/1.49    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK1,X2) != k10_relat_1(k7_relat_1(sK1,X1),X2) & r1_tarski(k10_relat_1(sK1,X2),X1)) & v1_relat_1(sK1))),
% 7.41/1.49    introduced(choice_axiom,[])).
% 7.41/1.49  
% 7.41/1.49  fof(f29,plain,(
% 7.41/1.49    (k10_relat_1(sK1,sK3) != k10_relat_1(k7_relat_1(sK1,sK2),sK3) & r1_tarski(k10_relat_1(sK1,sK3),sK2)) & v1_relat_1(sK1)),
% 7.41/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f28,f27])).
% 7.41/1.49  
% 7.41/1.49  fof(f47,plain,(
% 7.41/1.49    r1_tarski(k10_relat_1(sK1,sK3),sK2)),
% 7.41/1.49    inference(cnf_transformation,[],[f29])).
% 7.41/1.49  
% 7.41/1.49  fof(f5,axiom,(
% 7.41/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f16,plain,(
% 7.41/1.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 7.41/1.49    inference(ennf_transformation,[],[f5])).
% 7.41/1.49  
% 7.41/1.49  fof(f39,plain,(
% 7.41/1.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 7.41/1.49    inference(cnf_transformation,[],[f16])).
% 7.41/1.49  
% 7.41/1.49  fof(f4,axiom,(
% 7.41/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f26,plain,(
% 7.41/1.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.41/1.49    inference(nnf_transformation,[],[f4])).
% 7.41/1.49  
% 7.41/1.49  fof(f38,plain,(
% 7.41/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.41/1.49    inference(cnf_transformation,[],[f26])).
% 7.41/1.49  
% 7.41/1.49  fof(f6,axiom,(
% 7.41/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f40,plain,(
% 7.41/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.41/1.49    inference(cnf_transformation,[],[f6])).
% 7.41/1.49  
% 7.41/1.49  fof(f3,axiom,(
% 7.41/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f24,plain,(
% 7.41/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.41/1.49    inference(nnf_transformation,[],[f3])).
% 7.41/1.49  
% 7.41/1.49  fof(f25,plain,(
% 7.41/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.41/1.49    inference(flattening,[],[f24])).
% 7.41/1.49  
% 7.41/1.49  fof(f34,plain,(
% 7.41/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.41/1.49    inference(cnf_transformation,[],[f25])).
% 7.41/1.49  
% 7.41/1.49  fof(f53,plain,(
% 7.41/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.41/1.49    inference(equality_resolution,[],[f34])).
% 7.41/1.49  
% 7.41/1.49  fof(f11,axiom,(
% 7.41/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f18,plain,(
% 7.41/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.41/1.49    inference(ennf_transformation,[],[f11])).
% 7.41/1.49  
% 7.41/1.49  fof(f45,plain,(
% 7.41/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.41/1.49    inference(cnf_transformation,[],[f18])).
% 7.41/1.49  
% 7.41/1.49  fof(f2,axiom,(
% 7.41/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f15,plain,(
% 7.41/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.41/1.49    inference(ennf_transformation,[],[f2])).
% 7.41/1.49  
% 7.41/1.49  fof(f20,plain,(
% 7.41/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.41/1.49    inference(nnf_transformation,[],[f15])).
% 7.41/1.49  
% 7.41/1.49  fof(f21,plain,(
% 7.41/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.41/1.49    inference(rectify,[],[f20])).
% 7.41/1.49  
% 7.41/1.49  fof(f22,plain,(
% 7.41/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.41/1.49    introduced(choice_axiom,[])).
% 7.41/1.49  
% 7.41/1.49  fof(f23,plain,(
% 7.41/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.41/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 7.41/1.49  
% 7.41/1.49  fof(f32,plain,(
% 7.41/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.41/1.49    inference(cnf_transformation,[],[f23])).
% 7.41/1.49  
% 7.41/1.49  fof(f46,plain,(
% 7.41/1.49    v1_relat_1(sK1)),
% 7.41/1.49    inference(cnf_transformation,[],[f29])).
% 7.41/1.49  
% 7.41/1.49  fof(f10,axiom,(
% 7.41/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f17,plain,(
% 7.41/1.49    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.41/1.49    inference(ennf_transformation,[],[f10])).
% 7.41/1.49  
% 7.41/1.49  fof(f44,plain,(
% 7.41/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.41/1.49    inference(cnf_transformation,[],[f17])).
% 7.41/1.49  
% 7.41/1.49  fof(f7,axiom,(
% 7.41/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f41,plain,(
% 7.41/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.41/1.49    inference(cnf_transformation,[],[f7])).
% 7.41/1.49  
% 7.41/1.49  fof(f51,plain,(
% 7.41/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.41/1.49    inference(definition_unfolding,[],[f44,f41])).
% 7.41/1.49  
% 7.41/1.49  fof(f9,axiom,(
% 7.41/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f43,plain,(
% 7.41/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.41/1.49    inference(cnf_transformation,[],[f9])).
% 7.41/1.49  
% 7.41/1.49  fof(f8,axiom,(
% 7.41/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f42,plain,(
% 7.41/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.41/1.49    inference(cnf_transformation,[],[f8])).
% 7.41/1.49  
% 7.41/1.49  fof(f50,plain,(
% 7.41/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 7.41/1.49    inference(definition_unfolding,[],[f43,f41,f42])).
% 7.41/1.49  
% 7.41/1.49  fof(f1,axiom,(
% 7.41/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.49  
% 7.41/1.49  fof(f30,plain,(
% 7.41/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.41/1.49    inference(cnf_transformation,[],[f1])).
% 7.41/1.49  
% 7.41/1.49  fof(f49,plain,(
% 7.41/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.41/1.49    inference(definition_unfolding,[],[f30,f41,f41])).
% 7.41/1.49  
% 7.41/1.49  fof(f37,plain,(
% 7.41/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.41/1.49    inference(cnf_transformation,[],[f26])).
% 7.41/1.49  
% 7.41/1.49  fof(f36,plain,(
% 7.41/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.41/1.49    inference(cnf_transformation,[],[f25])).
% 7.41/1.49  
% 7.41/1.49  fof(f48,plain,(
% 7.41/1.49    k10_relat_1(sK1,sK3) != k10_relat_1(k7_relat_1(sK1,sK2),sK3)),
% 7.41/1.49    inference(cnf_transformation,[],[f29])).
% 7.41/1.49  
% 7.41/1.49  cnf(c_15,negated_conjecture,
% 7.41/1.49      ( r1_tarski(k10_relat_1(sK1,sK3),sK2) ),
% 7.41/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_578,plain,
% 7.41/1.49      ( r1_tarski(k10_relat_1(sK1,sK3),sK2) = iProver_top ),
% 7.41/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_9,plain,
% 7.41/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1) ),
% 7.41/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_582,plain,
% 7.41/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.41/1.49      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 7.41/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_7,plain,
% 7.41/1.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.41/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_584,plain,
% 7.41/1.49      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.41/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.41/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1742,plain,
% 7.41/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k1_xboole_0
% 7.41/1.49      | r1_tarski(X0,X2) != iProver_top ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_582,c_584]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_5410,plain,
% 7.41/1.49      ( k4_xboole_0(k4_xboole_0(k10_relat_1(sK1,sK3),X0),sK2) = k1_xboole_0 ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_578,c_1742]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_6107,plain,
% 7.41/1.49      ( r1_tarski(k4_xboole_0(k10_relat_1(sK1,sK3),X0),X1) != iProver_top
% 7.41/1.49      | r1_tarski(k1_xboole_0,X1) = iProver_top ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_5410,c_582]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_258,plain,
% 7.41/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.41/1.49      theory(equality) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_255,plain,( X0 = X0 ),theory(equality) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1950,plain,
% 7.41/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.41/1.49      inference(resolution,[status(thm)],[c_258,c_255]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_256,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1803,plain,
% 7.41/1.49      ( X0 != X1 | X1 = X0 ),
% 7.41/1.49      inference(resolution,[status(thm)],[c_256,c_255]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_2268,plain,
% 7.41/1.49      ( ~ r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 7.41/1.49      inference(resolution,[status(thm)],[c_1803,c_7]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_2448,plain,
% 7.41/1.49      ( ~ r1_tarski(X0,X1)
% 7.41/1.49      | ~ r1_tarski(k4_xboole_0(X0,X1),X2)
% 7.41/1.49      | r1_tarski(k1_xboole_0,X2) ),
% 7.41/1.49      inference(resolution,[status(thm)],[c_1950,c_2268]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_10,plain,
% 7.41/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.41/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_2647,plain,
% 7.41/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_xboole_0,X0) ),
% 7.41/1.49      inference(resolution,[status(thm)],[c_2448,c_10]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_6,plain,
% 7.41/1.49      ( r1_tarski(X0,X0) ),
% 7.41/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_2882,plain,
% 7.41/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.41/1.49      inference(resolution,[status(thm)],[c_2647,c_6]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_13,plain,
% 7.41/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.41/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_2,plain,
% 7.41/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.41/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_722,plain,
% 7.41/1.49      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,sK0(X0,X1)) ),
% 7.41/1.49      inference(resolution,[status(thm)],[c_13,c_2]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_779,plain,
% 7.41/1.49      ( ~ r1_tarski(X0,sK0(k4_xboole_0(X0,X1),X2))
% 7.41/1.49      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.41/1.49      inference(resolution,[status(thm)],[c_722,c_9]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_3095,plain,
% 7.41/1.49      ( r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) ),
% 7.41/1.49      inference(resolution,[status(thm)],[c_2882,c_779]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_3096,plain,
% 7.41/1.49      ( r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) = iProver_top ),
% 7.41/1.49      inference(predicate_to_equality,[status(thm)],[c_3095]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1263,plain,
% 7.41/1.49      ( k4_xboole_0(k10_relat_1(sK1,sK3),sK2) = k1_xboole_0 ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_578,c_584]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1739,plain,
% 7.41/1.49      ( r1_tarski(k10_relat_1(sK1,sK3),X0) != iProver_top
% 7.41/1.49      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_1263,c_582]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_2254,plain,
% 7.41/1.49      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_578,c_1739]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_5421,plain,
% 7.41/1.49      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),sK2) = k1_xboole_0 ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_2254,c_1742]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_6255,plain,
% 7.41/1.49      ( r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) != iProver_top
% 7.41/1.49      | r1_tarski(k1_xboole_0,X1) = iProver_top ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_5421,c_582]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_7974,plain,
% 7.41/1.49      ( r1_tarski(k1_xboole_0,X1) = iProver_top ),
% 7.41/1.49      inference(global_propositional_subsumption,
% 7.41/1.49                [status(thm)],
% 7.41/1.49                [c_6107,c_3096,c_6255]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_7975,plain,
% 7.41/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.41/1.49      inference(renaming,[status(thm)],[c_7974]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_7979,plain,
% 7.41/1.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_7975,c_584]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_16,negated_conjecture,
% 7.41/1.49      ( v1_relat_1(sK1) ),
% 7.41/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_577,plain,
% 7.41/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 7.41/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_12,plain,
% 7.41/1.49      ( ~ v1_relat_1(X0)
% 7.41/1.49      | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.41/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_580,plain,
% 7.41/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 7.41/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.41/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_11,plain,
% 7.41/1.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.41/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_634,plain,
% 7.41/1.49      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 7.41/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.41/1.49      inference(demodulation,[status(thm)],[c_580,c_11]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_4422,plain,
% 7.41/1.49      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_577,c_634]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_581,plain,
% 7.41/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.41/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1283,plain,
% 7.41/1.49      ( r1_tarski(k1_xboole_0,k10_relat_1(sK1,sK3)) = iProver_top ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_1263,c_581]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1447,plain,
% 7.41/1.49      ( k4_xboole_0(k1_xboole_0,k10_relat_1(sK1,sK3)) = k1_xboole_0 ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_1283,c_584]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1727,plain,
% 7.41/1.49      ( k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,k10_relat_1(sK1,sK3))) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_1447,c_11]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_4526,plain,
% 7.41/1.49      ( k10_relat_1(k7_relat_1(sK1,k1_xboole_0),sK3) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_4422,c_1727]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_12042,plain,
% 7.41/1.49      ( k10_relat_1(k7_relat_1(sK1,k1_xboole_0),sK3) = k1_xboole_0 ),
% 7.41/1.49      inference(demodulation,[status(thm)],[c_7979,c_4526]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_0,plain,
% 7.41/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.41/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_8,plain,
% 7.41/1.49      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.41/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_583,plain,
% 7.41/1.49      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 7.41/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.41/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1194,plain,
% 7.41/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 7.41/1.49      | r1_tarski(X1,k4_xboole_0(X1,X0)) = iProver_top ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_0,c_583]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1197,plain,
% 7.41/1.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) != k1_xboole_0
% 7.41/1.49      | r1_tarski(X1,k4_xboole_0(X1,X0)) = iProver_top ),
% 7.41/1.49      inference(light_normalisation,[status(thm)],[c_1194,c_11]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_4515,plain,
% 7.41/1.49      ( k10_relat_1(k7_relat_1(sK1,X0),X1) != k1_xboole_0
% 7.41/1.49      | r1_tarski(k10_relat_1(sK1,X1),k4_xboole_0(k10_relat_1(sK1,X1),X0)) = iProver_top ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_4422,c_1197]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_12126,plain,
% 7.41/1.49      ( r1_tarski(k10_relat_1(sK1,sK3),k4_xboole_0(k10_relat_1(sK1,sK3),k1_xboole_0)) = iProver_top ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_12042,c_4515]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_4,plain,
% 7.41/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.41/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_586,plain,
% 7.41/1.49      ( X0 = X1
% 7.41/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.41/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.41/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_2745,plain,
% 7.41/1.49      ( k4_xboole_0(X0,X1) = X2
% 7.41/1.49      | r1_tarski(X0,X2) != iProver_top
% 7.41/1.49      | r1_tarski(X2,k4_xboole_0(X0,X1)) != iProver_top ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_582,c_586]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_17895,plain,
% 7.41/1.49      ( k4_xboole_0(k10_relat_1(sK1,sK3),k1_xboole_0) = k10_relat_1(sK1,sK3)
% 7.41/1.49      | r1_tarski(k10_relat_1(sK1,sK3),k10_relat_1(sK1,sK3)) != iProver_top ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_12126,c_2745]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_895,plain,
% 7.41/1.49      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1284,plain,
% 7.41/1.49      ( k1_setfam_1(k1_enumset1(sK2,sK2,k10_relat_1(sK1,sK3))) = k4_xboole_0(k10_relat_1(sK1,sK3),k1_xboole_0) ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_1263,c_895]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_4525,plain,
% 7.41/1.49      ( k10_relat_1(k7_relat_1(sK1,sK2),sK3) = k4_xboole_0(k10_relat_1(sK1,sK3),k1_xboole_0) ),
% 7.41/1.49      inference(superposition,[status(thm)],[c_4422,c_1284]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_14,negated_conjecture,
% 7.41/1.49      ( k10_relat_1(sK1,sK3) != k10_relat_1(k7_relat_1(sK1,sK2),sK3) ),
% 7.41/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_5069,plain,
% 7.41/1.49      ( k4_xboole_0(k10_relat_1(sK1,sK3),k1_xboole_0) != k10_relat_1(sK1,sK3) ),
% 7.41/1.49      inference(demodulation,[status(thm)],[c_4525,c_14]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1520,plain,
% 7.41/1.49      ( r1_tarski(k10_relat_1(sK1,sK3),k10_relat_1(sK1,sK3)) ),
% 7.41/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(c_1523,plain,
% 7.41/1.49      ( r1_tarski(k10_relat_1(sK1,sK3),k10_relat_1(sK1,sK3)) = iProver_top ),
% 7.41/1.49      inference(predicate_to_equality,[status(thm)],[c_1520]) ).
% 7.41/1.49  
% 7.41/1.49  cnf(contradiction,plain,
% 7.41/1.49      ( $false ),
% 7.41/1.49      inference(minisat,[status(thm)],[c_17895,c_5069,c_1523]) ).
% 7.41/1.49  
% 7.41/1.49  
% 7.41/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.41/1.49  
% 7.41/1.49  ------                               Statistics
% 7.41/1.49  
% 7.41/1.49  ------ Selected
% 7.41/1.49  
% 7.41/1.49  total_time:                             0.522
% 7.41/1.49  
%------------------------------------------------------------------------------
