%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:04 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 114 expanded)
%              Number of clauses        :   46 (  53 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   15
%              Number of atoms          :  248 ( 455 expanded)
%              Number of equality atoms :  116 ( 169 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f18])).

fof(f31,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f30,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4356,plain,
    ( ~ r2_hidden(sK0(sK2,sK1,sK1),sK2)
    | ~ r2_hidden(sK0(sK2,sK1,sK1),sK1)
    | k1_setfam_1(k2_tarski(sK2,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4358,plain,
    ( r2_hidden(sK0(sK2,sK1,sK1),sK1)
    | k1_setfam_1(k2_tarski(sK2,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_189,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_664,plain,
    ( X0 != X1
    | X0 = k1_setfam_1(k2_tarski(X2,X3))
    | k1_setfam_1(k2_tarski(X2,X3)) != X1 ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_2589,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK1)) != X0
    | sK1 != X0
    | sK1 = k1_setfam_1(k2_tarski(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_2590,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK1)) != sK1
    | sK1 = k1_setfam_1(k2_tarski(sK2,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2589])).

cnf(c_192,plain,
    ( X0 != X1
    | X2 != X3
    | k7_relat_1(X0,X2) = k7_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_372,plain,
    ( k7_relat_1(sK3,sK1) = k7_relat_1(X0,X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_427,plain,
    ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,X0)
    | sK1 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_1057,plain,
    ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1)))
    | sK1 != k1_setfam_1(k2_tarski(sK2,sK1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_327,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_121,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_122,plain,
    ( r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_121])).

cnf(c_323,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_122])).

cnf(c_605,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = sK1
    | r2_hidden(sK0(X0,X1,sK1),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_327,c_323])).

cnf(c_932,plain,
    ( k1_setfam_1(k2_tarski(sK2,X0)) = sK1
    | r2_hidden(sK0(sK2,X0,sK1),sK2) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_605])).

cnf(c_934,plain,
    ( k1_setfam_1(k2_tarski(sK2,X0)) = sK1
    | r2_hidden(sK0(sK2,X0,sK1),sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_932])).

cnf(c_944,plain,
    ( r2_hidden(sK0(sK2,X0,sK1),sK2)
    | k1_setfam_1(k2_tarski(sK2,X0)) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_934])).

cnf(c_946,plain,
    ( r2_hidden(sK0(sK2,sK1,sK1),sK2)
    | k1_setfam_1(k2_tarski(sK2,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_375,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != X0
    | k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(sK3,sK1)
    | k7_relat_1(sK3,sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_887,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1)))
    | k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(sK3,sK1)
    | k7_relat_1(sK3,sK1) != k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_114,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_115,plain,
    ( k7_relat_1(sK3,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_689,plain,
    ( k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1))) = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(c_417,plain,
    ( k7_relat_1(X0,X1) != X2
    | k7_relat_1(k7_relat_1(sK3,sK2),sK1) != X2
    | k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_485,plain,
    ( k7_relat_1(X0,X1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    | k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(X0,X1)
    | k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_688,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    | k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1)))
    | k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1))) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_188,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_478,plain,
    ( k7_relat_1(sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_419,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(X0,X1)
    | k7_relat_1(sK3,sK2) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_477,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(k7_relat_1(sK3,sK2),X0)
    | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_479,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_407,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_369,plain,
    ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_355,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != X0
    | k7_relat_1(sK3,sK1) != X0
    | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_189])).

cnf(c_368,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(sK3,sK1)
    | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    | k7_relat_1(sK3,sK1) != k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_197,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_9,negated_conjecture,
    ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4356,c_4358,c_2590,c_1057,c_946,c_887,c_689,c_688,c_478,c_479,c_407,c_369,c_368,c_197,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:15:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.46/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/1.00  
% 3.46/1.00  ------  iProver source info
% 3.46/1.00  
% 3.46/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.46/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/1.00  git: non_committed_changes: false
% 3.46/1.00  git: last_make_outside_of_git: false
% 3.46/1.00  
% 3.46/1.00  ------ 
% 3.46/1.00  ------ Parsing...
% 3.46/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/1.00  ------ Proving...
% 3.46/1.00  ------ Problem Properties 
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  clauses                                 10
% 3.46/1.00  conjectures                             1
% 3.46/1.00  EPR                                     1
% 3.46/1.00  Horn                                    8
% 3.46/1.00  unary                                   3
% 3.46/1.00  binary                                  3
% 3.46/1.00  lits                                    22
% 3.46/1.00  lits eq                                 6
% 3.46/1.00  fd_pure                                 0
% 3.46/1.00  fd_pseudo                               0
% 3.46/1.00  fd_cond                                 0
% 3.46/1.00  fd_pseudo_cond                          3
% 3.46/1.00  AC symbols                              0
% 3.46/1.00  
% 3.46/1.00  ------ Input Options Time Limit: Unbounded
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  ------ 
% 3.46/1.00  Current options:
% 3.46/1.00  ------ 
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  ------ Proving...
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  % SZS status Theorem for theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  fof(f3,axiom,(
% 3.46/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f13,plain,(
% 3.46/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.46/1.00    inference(nnf_transformation,[],[f3])).
% 3.46/1.00  
% 3.46/1.00  fof(f14,plain,(
% 3.46/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.46/1.00    inference(flattening,[],[f13])).
% 3.46/1.00  
% 3.46/1.00  fof(f15,plain,(
% 3.46/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.46/1.00    inference(rectify,[],[f14])).
% 3.46/1.00  
% 3.46/1.00  fof(f16,plain,(
% 3.46/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.46/1.00    introduced(choice_axiom,[])).
% 3.46/1.00  
% 3.46/1.00  fof(f17,plain,(
% 3.46/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.46/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.46/1.00  
% 3.46/1.00  fof(f27,plain,(
% 3.46/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f17])).
% 3.46/1.00  
% 3.46/1.00  fof(f4,axiom,(
% 3.46/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f28,plain,(
% 3.46/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.46/1.00    inference(cnf_transformation,[],[f4])).
% 3.46/1.00  
% 3.46/1.00  fof(f34,plain,(
% 3.46/1.00    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.46/1.00    inference(definition_unfolding,[],[f27,f28])).
% 3.46/1.00  
% 3.46/1.00  fof(f26,plain,(
% 3.46/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f17])).
% 3.46/1.00  
% 3.46/1.00  fof(f35,plain,(
% 3.46/1.00    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.46/1.00    inference(definition_unfolding,[],[f26,f28])).
% 3.46/1.00  
% 3.46/1.00  fof(f25,plain,(
% 3.46/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f17])).
% 3.46/1.00  
% 3.46/1.00  fof(f36,plain,(
% 3.46/1.00    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.46/1.00    inference(definition_unfolding,[],[f25,f28])).
% 3.46/1.00  
% 3.46/1.00  fof(f2,axiom,(
% 3.46/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f8,plain,(
% 3.46/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.46/1.00    inference(unused_predicate_definition_removal,[],[f2])).
% 3.46/1.00  
% 3.46/1.00  fof(f9,plain,(
% 3.46/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.46/1.00    inference(ennf_transformation,[],[f8])).
% 3.46/1.00  
% 3.46/1.00  fof(f21,plain,(
% 3.46/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f9])).
% 3.46/1.00  
% 3.46/1.00  fof(f6,conjecture,(
% 3.46/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 3.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f7,negated_conjecture,(
% 3.46/1.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 3.46/1.00    inference(negated_conjecture,[],[f6])).
% 3.46/1.00  
% 3.46/1.00  fof(f11,plain,(
% 3.46/1.00    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 3.46/1.00    inference(ennf_transformation,[],[f7])).
% 3.46/1.00  
% 3.46/1.00  fof(f12,plain,(
% 3.46/1.00    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 3.46/1.00    inference(flattening,[],[f11])).
% 3.46/1.00  
% 3.46/1.00  fof(f18,plain,(
% 3.46/1.00    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3))),
% 3.46/1.00    introduced(choice_axiom,[])).
% 3.46/1.00  
% 3.46/1.00  fof(f19,plain,(
% 3.46/1.00    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3)),
% 3.46/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f18])).
% 3.46/1.00  
% 3.46/1.00  fof(f31,plain,(
% 3.46/1.00    r1_tarski(sK1,sK2)),
% 3.46/1.00    inference(cnf_transformation,[],[f19])).
% 3.46/1.00  
% 3.46/1.00  fof(f5,axiom,(
% 3.46/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 3.46/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f10,plain,(
% 3.46/1.00    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.46/1.00    inference(ennf_transformation,[],[f5])).
% 3.46/1.00  
% 3.46/1.00  fof(f29,plain,(
% 3.46/1.00    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f10])).
% 3.46/1.00  
% 3.46/1.00  fof(f40,plain,(
% 3.46/1.00    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 3.46/1.00    inference(definition_unfolding,[],[f29,f28])).
% 3.46/1.00  
% 3.46/1.00  fof(f30,plain,(
% 3.46/1.00    v1_relat_1(sK3)),
% 3.46/1.00    inference(cnf_transformation,[],[f19])).
% 3.46/1.00  
% 3.46/1.00  fof(f32,plain,(
% 3.46/1.00    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)),
% 3.46/1.00    inference(cnf_transformation,[],[f19])).
% 3.46/1.00  
% 3.46/1.00  cnf(c_2,plain,
% 3.46/1.00      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.46/1.00      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.46/1.00      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.46/1.00      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
% 3.46/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_4356,plain,
% 3.46/1.00      ( ~ r2_hidden(sK0(sK2,sK1,sK1),sK2)
% 3.46/1.00      | ~ r2_hidden(sK0(sK2,sK1,sK1),sK1)
% 3.46/1.00      | k1_setfam_1(k2_tarski(sK2,sK1)) = sK1 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_3,plain,
% 3.46/1.00      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.46/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.46/1.00      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
% 3.46/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_4358,plain,
% 3.46/1.00      ( r2_hidden(sK0(sK2,sK1,sK1),sK1)
% 3.46/1.00      | k1_setfam_1(k2_tarski(sK2,sK1)) = sK1 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_189,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_664,plain,
% 3.46/1.00      ( X0 != X1
% 3.46/1.00      | X0 = k1_setfam_1(k2_tarski(X2,X3))
% 3.46/1.00      | k1_setfam_1(k2_tarski(X2,X3)) != X1 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_189]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_2589,plain,
% 3.46/1.00      ( k1_setfam_1(k2_tarski(sK2,sK1)) != X0
% 3.46/1.00      | sK1 != X0
% 3.46/1.00      | sK1 = k1_setfam_1(k2_tarski(sK2,sK1)) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_664]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_2590,plain,
% 3.46/1.00      ( k1_setfam_1(k2_tarski(sK2,sK1)) != sK1
% 3.46/1.00      | sK1 = k1_setfam_1(k2_tarski(sK2,sK1))
% 3.46/1.00      | sK1 != sK1 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_2589]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_192,plain,
% 3.46/1.00      ( X0 != X1 | X2 != X3 | k7_relat_1(X0,X2) = k7_relat_1(X1,X3) ),
% 3.46/1.00      theory(equality) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_372,plain,
% 3.46/1.00      ( k7_relat_1(sK3,sK1) = k7_relat_1(X0,X1) | sK1 != X1 | sK3 != X0 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_192]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_427,plain,
% 3.46/1.00      ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,X0)
% 3.46/1.00      | sK1 != X0
% 3.46/1.00      | sK3 != sK3 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_372]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1057,plain,
% 3.46/1.00      ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1)))
% 3.46/1.00      | sK1 != k1_setfam_1(k2_tarski(sK2,sK1))
% 3.46/1.00      | sK3 != sK3 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_427]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_4,plain,
% 3.46/1.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.46/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.46/1.00      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ),
% 3.46/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_327,plain,
% 3.46/1.00      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 3.46/1.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 3.46/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1,plain,
% 3.46/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.46/1.00      inference(cnf_transformation,[],[f21]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_10,negated_conjecture,
% 3.46/1.00      ( r1_tarski(sK1,sK2) ),
% 3.46/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_121,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | sK2 != X2 | sK1 != X1 ),
% 3.46/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_10]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_122,plain,
% 3.46/1.00      ( r2_hidden(X0,sK2) | ~ r2_hidden(X0,sK1) ),
% 3.46/1.00      inference(unflattening,[status(thm)],[c_121]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_323,plain,
% 3.46/1.00      ( r2_hidden(X0,sK2) = iProver_top
% 3.46/1.00      | r2_hidden(X0,sK1) != iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_122]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_605,plain,
% 3.46/1.00      ( k1_setfam_1(k2_tarski(X0,X1)) = sK1
% 3.46/1.00      | r2_hidden(sK0(X0,X1,sK1),X0) = iProver_top
% 3.46/1.00      | r2_hidden(sK0(X0,X1,sK1),sK2) = iProver_top ),
% 3.46/1.00      inference(superposition,[status(thm)],[c_327,c_323]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_932,plain,
% 3.46/1.00      ( k1_setfam_1(k2_tarski(sK2,X0)) = sK1
% 3.46/1.00      | r2_hidden(sK0(sK2,X0,sK1),sK2) = iProver_top
% 3.46/1.00      | iProver_top != iProver_top ),
% 3.46/1.00      inference(equality_factoring,[status(thm)],[c_605]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_934,plain,
% 3.46/1.00      ( k1_setfam_1(k2_tarski(sK2,X0)) = sK1
% 3.46/1.00      | r2_hidden(sK0(sK2,X0,sK1),sK2) = iProver_top ),
% 3.46/1.00      inference(equality_resolution_simp,[status(thm)],[c_932]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_944,plain,
% 3.46/1.00      ( r2_hidden(sK0(sK2,X0,sK1),sK2)
% 3.46/1.00      | k1_setfam_1(k2_tarski(sK2,X0)) = sK1 ),
% 3.46/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_934]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_946,plain,
% 3.46/1.00      ( r2_hidden(sK0(sK2,sK1,sK1),sK2)
% 3.46/1.00      | k1_setfam_1(k2_tarski(sK2,sK1)) = sK1 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_944]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_375,plain,
% 3.46/1.00      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != X0
% 3.46/1.00      | k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(sK3,sK1)
% 3.46/1.00      | k7_relat_1(sK3,sK1) != X0 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_189]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_887,plain,
% 3.46/1.00      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1)))
% 3.46/1.00      | k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(sK3,sK1)
% 3.46/1.00      | k7_relat_1(sK3,sK1) != k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1))) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_375]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_8,plain,
% 3.46/1.00      ( ~ v1_relat_1(X0)
% 3.46/1.00      | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.46/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_11,negated_conjecture,
% 3.46/1.00      ( v1_relat_1(sK3) ),
% 3.46/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_114,plain,
% 3.46/1.00      ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 3.46/1.00      | sK3 != X0 ),
% 3.46/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_115,plain,
% 3.46/1.00      ( k7_relat_1(sK3,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
% 3.46/1.00      inference(unflattening,[status(thm)],[c_114]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_689,plain,
% 3.46/1.00      ( k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1))) = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_115]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_417,plain,
% 3.46/1.00      ( k7_relat_1(X0,X1) != X2
% 3.46/1.00      | k7_relat_1(k7_relat_1(sK3,sK2),sK1) != X2
% 3.46/1.00      | k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(X0,X1) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_189]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_485,plain,
% 3.46/1.00      ( k7_relat_1(X0,X1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
% 3.46/1.00      | k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(X0,X1)
% 3.46/1.00      | k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_417]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_688,plain,
% 3.46/1.00      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
% 3.46/1.00      | k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1)))
% 3.46/1.00      | k7_relat_1(sK3,k1_setfam_1(k2_tarski(sK2,sK1))) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_485]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_188,plain,( X0 = X0 ),theory(equality) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_478,plain,
% 3.46/1.00      ( k7_relat_1(sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_188]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_419,plain,
% 3.46/1.00      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(X0,X1)
% 3.46/1.00      | k7_relat_1(sK3,sK2) != X0
% 3.46/1.00      | sK1 != X1 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_192]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_477,plain,
% 3.46/1.00      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(k7_relat_1(sK3,sK2),X0)
% 3.46/1.00      | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2)
% 3.46/1.00      | sK1 != X0 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_419]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_479,plain,
% 3.46/1.00      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
% 3.46/1.00      | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2)
% 3.46/1.00      | sK1 != sK1 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_477]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_407,plain,
% 3.46/1.00      ( sK3 = sK3 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_188]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_369,plain,
% 3.46/1.00      ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,sK1) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_188]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_355,plain,
% 3.46/1.00      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != X0
% 3.46/1.00      | k7_relat_1(sK3,sK1) != X0
% 3.46/1.00      | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_189]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_368,plain,
% 3.46/1.00      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(sK3,sK1)
% 3.46/1.00      | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
% 3.46/1.00      | k7_relat_1(sK3,sK1) != k7_relat_1(sK3,sK1) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_355]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_197,plain,
% 3.46/1.00      ( sK1 = sK1 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_188]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_9,negated_conjecture,
% 3.46/1.00      ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
% 3.46/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(contradiction,plain,
% 3.46/1.00      ( $false ),
% 3.46/1.00      inference(minisat,
% 3.46/1.00                [status(thm)],
% 3.46/1.00                [c_4356,c_4358,c_2590,c_1057,c_946,c_887,c_689,c_688,
% 3.46/1.00                 c_478,c_479,c_407,c_369,c_368,c_197,c_9]) ).
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  ------                               Statistics
% 3.46/1.00  
% 3.46/1.00  ------ Selected
% 3.46/1.00  
% 3.46/1.00  total_time:                             0.182
% 3.46/1.00  
%------------------------------------------------------------------------------
