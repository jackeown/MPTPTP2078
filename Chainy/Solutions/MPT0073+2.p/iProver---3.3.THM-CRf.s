%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0073+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:18 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 103 expanded)
%              Number of clauses        :   31 (  34 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  230 ( 312 expanded)
%              Number of equality atoms :   65 ( 107 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f132,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f306,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f132])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f120])).

fof(f226,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f130,f226])).

fof(f300,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f227])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f234,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f234])).

fof(f310,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f235])).

fof(f482,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f310])).

fof(f108,conjecture,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f109,negated_conjecture,(
    ~ ! [X0] :
        ( ~ ( r1_xboole_0(X0,X0)
            & k1_xboole_0 != X0 )
        & ~ ( k1_xboole_0 = X0
            & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(negated_conjecture,[],[f108])).

fof(f182,plain,(
    ? [X0] :
      ( ( r1_xboole_0(X0,X0)
        & k1_xboole_0 != X0 )
      | ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f109])).

fof(f242,plain,
    ( ? [X0] :
        ( ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
        | ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) )
   => ( ( r1_xboole_0(sK15,sK15)
        & k1_xboole_0 != sK15 )
      | ( k1_xboole_0 = sK15
        & ~ r1_xboole_0(sK15,sK15) ) ) ),
    introduced(choice_axiom,[])).

fof(f243,plain,
    ( ( r1_xboole_0(sK15,sK15)
      & k1_xboole_0 != sK15 )
    | ( k1_xboole_0 = sK15
      & ~ r1_xboole_0(sK15,sK15) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f182,f242])).

fof(f392,plain,
    ( r1_xboole_0(sK15,sK15)
    | k1_xboole_0 = sK15 ),
    inference(cnf_transformation,[],[f243])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f251,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f467,plain,
    ( r1_xboole_0(sK15,sK15)
    | o_0_0_xboole_0 = sK15 ),
    inference(definition_unfolding,[],[f392,f251])).

fof(f106,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f180,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f181,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f180])).

fof(f387,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f181])).

fof(f107,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f388,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f107])).

fof(f466,plain,(
    ! [X0] : r1_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f388,f251])).

fof(f112,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f112])).

fof(f395,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f184])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f128,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f220,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f128])).

fof(f221,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f222,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f220,f221])).

fof(f292,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK7(X0,X1),X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f222])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f280,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f410,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f280,f251])).

fof(f389,plain,
    ( k1_xboole_0 != sK15
    | ~ r1_xboole_0(sK15,sK15) ),
    inference(cnf_transformation,[],[f243])).

fof(f469,plain,
    ( o_0_0_xboole_0 != sK15
    | ~ r1_xboole_0(sK15,sK15) ),
    inference(definition_unfolding,[],[f389,f251])).

cnf(c_57,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f306])).

cnf(c_52,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f300])).

cnf(c_680,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r1_xboole_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_57,c_52])).

cnf(c_681,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_680])).

cnf(c_5733,plain,
    ( ~ r1_xboole_0(X0,sK15)
    | ~ r2_hidden(sK7(o_0_0_xboole_0,sK15),X0)
    | ~ r2_hidden(sK7(o_0_0_xboole_0,sK15),sK15) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_7338,plain,
    ( ~ r1_xboole_0(sK15,sK15)
    | ~ r2_hidden(sK7(o_0_0_xboole_0,sK15),sK15) ),
    inference(instantiation,[status(thm)],[c_5733])).

cnf(c_66,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f482])).

cnf(c_4430,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_142,negated_conjecture,
    ( r1_xboole_0(sK15,sK15)
    | o_0_0_xboole_0 = sK15 ),
    inference(cnf_transformation,[],[f467])).

cnf(c_4386,plain,
    ( o_0_0_xboole_0 = sK15
    | r1_xboole_0(sK15,sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_140,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X3,X1) ),
    inference(cnf_transformation,[],[f387])).

cnf(c_4388,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X2,X3) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X3,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_5393,plain,
    ( sK15 = o_0_0_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,sK15) != iProver_top
    | r1_tarski(X1,sK15) != iProver_top ),
    inference(superposition,[status(thm)],[c_4386,c_4388])).

cnf(c_5501,plain,
    ( sK15 = o_0_0_xboole_0
    | r1_xboole_0(sK15,X0) = iProver_top
    | r1_tarski(X0,sK15) != iProver_top ),
    inference(superposition,[status(thm)],[c_4430,c_5393])).

cnf(c_5523,plain,
    ( sK15 = o_0_0_xboole_0
    | r1_xboole_0(sK15,sK15) = iProver_top ),
    inference(superposition,[status(thm)],[c_4430,c_5501])).

cnf(c_141,plain,
    ( r1_xboole_0(X0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f466])).

cnf(c_173,plain,
    ( r1_xboole_0(X0,o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141])).

cnf(c_175,plain,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_2338,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5328,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(sK15,sK15)
    | sK15 != X0
    | sK15 != X1 ),
    inference(instantiation,[status(thm)],[c_2338])).

cnf(c_5329,plain,
    ( sK15 != X0
    | sK15 != X1
    | r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(sK15,sK15) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5328])).

cnf(c_5331,plain,
    ( sK15 != o_0_0_xboole_0
    | r1_xboole_0(sK15,sK15) = iProver_top
    | r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5329])).

cnf(c_5797,plain,
    ( r1_xboole_0(sK15,sK15) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5523,c_175,c_5331])).

cnf(c_148,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f395])).

cnf(c_5755,plain,
    ( ~ r2_hidden(sK7(o_0_0_xboole_0,sK15),o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_47,plain,
    ( r2_hidden(sK7(X0,X1),X1)
    | r2_hidden(sK7(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f292])).

cnf(c_5532,plain,
    ( r2_hidden(sK7(o_0_0_xboole_0,sK15),sK15)
    | r2_hidden(sK7(o_0_0_xboole_0,sK15),o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK15 ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_34,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f410])).

cnf(c_145,negated_conjecture,
    ( ~ r1_xboole_0(sK15,sK15)
    | o_0_0_xboole_0 != sK15 ),
    inference(cnf_transformation,[],[f469])).

cnf(c_153,plain,
    ( o_0_0_xboole_0 != sK15
    | r1_xboole_0(sK15,sK15) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7338,c_5797,c_5755,c_5532,c_34,c_142,c_153])).

%------------------------------------------------------------------------------
