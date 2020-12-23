%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:30 EST 2020

% Result     : CounterSatisfiable 2.02s
% Output     : Saturation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 445 expanded)
%              Number of clauses        :   86 ( 194 expanded)
%              Number of leaves         :   18 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  313 (1421 expanded)
%              Number of equality atoms :   76 ( 217 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
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

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ~ ( r1_xboole_0(X0,X1)
            & r1_tarski(X2,X1)
            & r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f16])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X2,X0)
        & ~ v1_xboole_0(X2) )
   => ( r1_xboole_0(sK2,sK3)
      & r1_tarski(sK4,sK3)
      & r1_tarski(sK4,sK2)
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( r1_xboole_0(sK2,sK3)
    & r1_tarski(sK4,sK3)
    & r1_tarski(sK4,sK2)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f23])).

fof(f38,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    r1_tarski(sK4,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_161,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_159,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_325,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_328,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_327,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_1219,plain,
    ( X0_40 != X1_40
    | X1_40 = X0_40 ),
    inference(resolution,[status(thm)],[c_328,c_327])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_323,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | k3_xboole_0(X0_40,X1_40) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1451,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | X2_40 != k1_xboole_0
    | k3_xboole_0(X0_40,X1_40) = X2_40 ),
    inference(resolution,[status(thm)],[c_323,c_328])).

cnf(c_1941,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | X2_40 = k3_xboole_0(X0_40,X1_40)
    | X2_40 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1219,c_1451])).

cnf(c_330,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X2_40,X3_40)
    | X2_40 != X0_40
    | X3_40 != X1_40 ),
    theory(equality)).

cnf(c_2117,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X2_40,X3_40)
    | ~ r1_xboole_0(X4_40,k3_xboole_0(X0_40,X1_40))
    | X2_40 != X4_40
    | X3_40 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1941,c_330])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_318,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | ~ r2_hidden(X0_39,k3_xboole_0(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_320,plain,
    ( r1_xboole_0(X0_40,X1_40)
    | r2_hidden(sK0(X0_40,X1_40),X1_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1154,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X2_40,k3_xboole_0(X0_40,X1_40)) ),
    inference(resolution,[status(thm)],[c_318,c_320])).

cnf(c_3385,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X2_40,X3_40)
    | X2_40 != X4_40
    | X3_40 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2117,c_1154])).

cnf(c_1834,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | X2_40 != X3_40
    | X3_40 != k1_xboole_0
    | k3_xboole_0(X0_40,X1_40) = X2_40 ),
    inference(resolution,[status(thm)],[c_1451,c_328])).

cnf(c_2538,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | ~ r1_xboole_0(X2_40,X3_40)
    | X4_40 != k3_xboole_0(X2_40,X3_40)
    | k3_xboole_0(X0_40,X1_40) = X4_40 ),
    inference(resolution,[status(thm)],[c_1834,c_323])).

cnf(c_2795,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | ~ r1_xboole_0(X2_40,X3_40)
    | k3_xboole_0(X0_40,X1_40) = k3_xboole_0(X2_40,X3_40) ),
    inference(resolution,[status(thm)],[c_2538,c_327])).

cnf(c_1311,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X2_40,X1_40)
    | X2_40 != X0_40 ),
    inference(resolution,[status(thm)],[c_330,c_327])).

cnf(c_2115,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X2_40,X3_40)
    | ~ r1_xboole_0(k3_xboole_0(X0_40,X1_40),X3_40)
    | X2_40 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1941,c_1311])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_319,plain,
    ( r1_xboole_0(X0_40,X1_40)
    | r2_hidden(sK0(X0_40,X1_40),X0_40) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1150,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(k3_xboole_0(X0_40,X1_40),X2_40) ),
    inference(resolution,[status(thm)],[c_318,c_319])).

cnf(c_2425,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X2_40,X3_40)
    | X2_40 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2115,c_1150])).

cnf(c_329,plain,
    ( ~ r2_hidden(X0_39,X0_40)
    | r2_hidden(X1_39,X1_40)
    | X1_40 != X0_40
    | X1_39 != X0_39 ),
    theory(equality)).

cnf(c_326,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_1230,plain,
    ( ~ r2_hidden(X0_39,X0_40)
    | r2_hidden(X0_39,X1_40)
    | X1_40 != X0_40 ),
    inference(resolution,[status(thm)],[c_329,c_326])).

cnf(c_1956,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | ~ r2_hidden(X0_39,X2_40)
    | r2_hidden(X0_39,k3_xboole_0(X0_40,X1_40))
    | X2_40 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1230,c_1451])).

cnf(c_2250,plain,
    ( ~ r2_hidden(X0_39,X2_40)
    | ~ r1_xboole_0(X0_40,X1_40)
    | X2_40 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1956,c_318])).

cnf(c_2251,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | ~ r2_hidden(X0_39,X2_40)
    | X2_40 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2250])).

cnf(c_2109,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | X2_40 = X3_40
    | X3_40 != k3_xboole_0(X0_40,X1_40)
    | X2_40 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1941,c_328])).

cnf(c_1936,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | k1_xboole_0 = k3_xboole_0(X0_40,X1_40) ),
    inference(resolution,[status(thm)],[c_1219,c_323])).

cnf(c_1989,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | X2_40 != k3_xboole_0(X0_40,X1_40)
    | k1_xboole_0 = X2_40 ),
    inference(resolution,[status(thm)],[c_1936,c_328])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_321,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | ~ r2_hidden(X0_39,X0_40)
    | ~ r2_hidden(X0_39,X1_40) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1530,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X2_40,X1_40)
    | ~ r2_hidden(sK0(X2_40,X1_40),X0_40) ),
    inference(resolution,[status(thm)],[c_321,c_320])).

cnf(c_1763,plain,
    ( ~ r1_xboole_0(X0_40,X0_40)
    | r1_xboole_0(X1_40,X0_40) ),
    inference(resolution,[status(thm)],[c_1530,c_320])).

cnf(c_1953,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r2_hidden(X0_39,k3_xboole_0(X0_40,X1_40))
    | ~ r2_hidden(X0_39,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1230,c_323])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_316,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_634,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_627,plain,
    ( k3_xboole_0(X0_40,X1_40) = k1_xboole_0
    | r1_xboole_0(X0_40,X1_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_1015,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_634,c_627])).

cnf(c_632,plain,
    ( r1_xboole_0(X0_40,X1_40) != iProver_top
    | r2_hidden(X0_39,k3_xboole_0(X0_40,X1_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_1278,plain,
    ( r1_xboole_0(sK2,sK3) != iProver_top
    | r2_hidden(X0_39,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1015,c_632])).

cnf(c_1293,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | ~ r2_hidden(X0_39,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1278])).

cnf(c_1997,plain,
    ( ~ r2_hidden(X0_39,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1953,c_10,c_1293])).

cnf(c_2011,plain,
    ( r1_xboole_0(X0_40,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1997,c_320])).

cnf(c_2009,plain,
    ( r1_xboole_0(k1_xboole_0,X0_40) ),
    inference(resolution,[status(thm)],[c_1997,c_319])).

cnf(c_1528,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X1_40,X2_40)
    | ~ r2_hidden(sK0(X1_40,X2_40),X0_40) ),
    inference(resolution,[status(thm)],[c_321,c_319])).

cnf(c_1550,plain,
    ( ~ r1_xboole_0(X0_40,X0_40)
    | r1_xboole_0(X0_40,X1_40) ),
    inference(resolution,[status(thm)],[c_1528,c_319])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_317,plain,
    ( r1_xboole_0(X0_40,X1_40)
    | r2_hidden(sK1(X0_40,X1_40),k3_xboole_0(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1524,plain,
    ( r1_xboole_0(X0_40,X1_40)
    | ~ r1_xboole_0(X2_40,k3_xboole_0(X0_40,X1_40))
    | ~ r2_hidden(sK1(X0_40,X1_40),X2_40) ),
    inference(resolution,[status(thm)],[c_321,c_317])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK4,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_193,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK4 != X1
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_194,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_313,plain,
    ( ~ r2_hidden(X0_39,sK4)
    | r2_hidden(X0_39,sK2) ),
    inference(subtyping,[status(esa)],[c_194])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_181,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK4 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_182,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_314,plain,
    ( ~ r2_hidden(X0_39,sK4)
    | r2_hidden(X0_39,sK3) ),
    inference(subtyping,[status(esa)],[c_182])).

cnf(c_635,plain,
    ( r2_hidden(X0_39,sK4) != iProver_top
    | r2_hidden(X0_39,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_17,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_353,plain,
    ( r2_hidden(X0_39,sK4) != iProver_top
    | r2_hidden(X0_39,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_356,plain,
    ( r2_hidden(X0_39,sK4) != iProver_top
    | r2_hidden(X0_39,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_802,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | ~ r2_hidden(X0_39,sK3)
    | ~ r2_hidden(X0_39,sK2) ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_803,plain,
    ( r1_xboole_0(sK2,sK3) != iProver_top
    | r2_hidden(X0_39,sK3) != iProver_top
    | r2_hidden(X0_39,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_881,plain,
    ( r2_hidden(X0_39,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_635,c_17,c_353,c_356,c_803])).

cnf(c_883,plain,
    ( ~ r2_hidden(X0_39,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_881])).

cnf(c_898,plain,
    ( ~ r2_hidden(X0_39,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_883])).

cnf(c_910,plain,
    ( r1_xboole_0(sK4,X0_40) ),
    inference(resolution,[status(thm)],[c_898,c_319])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_322,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1022,plain,
    ( r1_xboole_0(X0_40,sK4) ),
    inference(resolution,[status(thm)],[c_910,c_322])).

cnf(c_790,plain,
    ( r1_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_322,c_316])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_324,plain,
    ( r1_xboole_0(X0_40,X1_40)
    | k3_xboole_0(X0_40,X1_40) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_176,plain,
    ( sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_315,plain,
    ( sK4 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_176])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:23:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.02/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/0.99  
% 2.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.02/0.99  
% 2.02/0.99  ------  iProver source info
% 2.02/0.99  
% 2.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.02/0.99  git: non_committed_changes: false
% 2.02/0.99  git: last_make_outside_of_git: false
% 2.02/0.99  
% 2.02/0.99  ------ 
% 2.02/0.99  ------ Parsing...
% 2.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.02/0.99  
% 2.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.02/0.99  
% 2.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.02/0.99  
% 2.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.02/0.99  ------ Proving...
% 2.02/0.99  ------ Problem Properties 
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  clauses                                 12
% 2.02/0.99  conjectures                             1
% 2.02/0.99  EPR                                     6
% 2.02/0.99  Horn                                    9
% 2.02/0.99  unary                                   2
% 2.02/0.99  binary                                  9
% 2.02/0.99  lits                                    23
% 2.02/0.99  lits eq                                 3
% 2.02/0.99  fd_pure                                 0
% 2.02/0.99  fd_pseudo                               0
% 2.02/0.99  fd_cond                                 0
% 2.02/0.99  fd_pseudo_cond                          0
% 2.02/0.99  AC symbols                              0
% 2.02/0.99  
% 2.02/0.99  ------ Input Options Time Limit: Unbounded
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  ------ 
% 2.02/0.99  Current options:
% 2.02/0.99  ------ 
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  ------ Proving...
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 2.02/0.99  
% 2.02/0.99  % SZS output start Saturation for theBenchmark.p
% 2.02/0.99  
% 2.02/0.99  fof(f2,axiom,(
% 2.02/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f18,plain,(
% 2.02/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.02/0.99    inference(nnf_transformation,[],[f2])).
% 2.02/0.99  
% 2.02/0.99  fof(f26,plain,(
% 2.02/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f18])).
% 2.02/0.99  
% 2.02/0.99  fof(f6,axiom,(
% 2.02/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f10,plain,(
% 2.02/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.02/0.99    inference(rectify,[],[f6])).
% 2.02/0.99  
% 2.02/0.99  fof(f15,plain,(
% 2.02/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.02/0.99    inference(ennf_transformation,[],[f10])).
% 2.02/0.99  
% 2.02/0.99  fof(f21,plain,(
% 2.02/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 2.02/0.99    introduced(choice_axiom,[])).
% 2.02/0.99  
% 2.02/0.99  fof(f22,plain,(
% 2.02/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f21])).
% 2.02/0.99  
% 2.02/0.99  fof(f34,plain,(
% 2.02/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.02/0.99    inference(cnf_transformation,[],[f22])).
% 2.02/0.99  
% 2.02/0.99  fof(f5,axiom,(
% 2.02/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f9,plain,(
% 2.02/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.02/0.99    inference(rectify,[],[f5])).
% 2.02/0.99  
% 2.02/0.99  fof(f14,plain,(
% 2.02/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.02/0.99    inference(ennf_transformation,[],[f9])).
% 2.02/0.99  
% 2.02/0.99  fof(f19,plain,(
% 2.02/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.02/0.99    introduced(choice_axiom,[])).
% 2.02/0.99  
% 2.02/0.99  fof(f20,plain,(
% 2.02/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f19])).
% 2.02/0.99  
% 2.02/0.99  fof(f31,plain,(
% 2.02/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f20])).
% 2.02/0.99  
% 2.02/0.99  fof(f30,plain,(
% 2.02/0.99    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f20])).
% 2.02/0.99  
% 2.02/0.99  fof(f32,plain,(
% 2.02/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f20])).
% 2.02/0.99  
% 2.02/0.99  fof(f7,conjecture,(
% 2.02/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f8,negated_conjecture,(
% 2.02/0.99    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 2.02/0.99    inference(negated_conjecture,[],[f7])).
% 2.02/0.99  
% 2.02/0.99  fof(f16,plain,(
% 2.02/0.99    ? [X0,X1,X2] : ((r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)) & ~v1_xboole_0(X2))),
% 2.02/0.99    inference(ennf_transformation,[],[f8])).
% 2.02/0.99  
% 2.02/0.99  fof(f17,plain,(
% 2.02/0.99    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2))),
% 2.02/0.99    inference(flattening,[],[f16])).
% 2.02/0.99  
% 2.02/0.99  fof(f23,plain,(
% 2.02/0.99    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2)) => (r1_xboole_0(sK2,sK3) & r1_tarski(sK4,sK3) & r1_tarski(sK4,sK2) & ~v1_xboole_0(sK4))),
% 2.02/0.99    introduced(choice_axiom,[])).
% 2.02/0.99  
% 2.02/0.99  fof(f24,plain,(
% 2.02/0.99    r1_xboole_0(sK2,sK3) & r1_tarski(sK4,sK3) & r1_tarski(sK4,sK2) & ~v1_xboole_0(sK4)),
% 2.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f23])).
% 2.02/0.99  
% 2.02/0.99  fof(f38,plain,(
% 2.02/0.99    r1_xboole_0(sK2,sK3)),
% 2.02/0.99    inference(cnf_transformation,[],[f24])).
% 2.02/0.99  
% 2.02/0.99  fof(f33,plain,(
% 2.02/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f22])).
% 2.02/0.99  
% 2.02/0.99  fof(f1,axiom,(
% 2.02/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f11,plain,(
% 2.02/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.02/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.02/0.99  
% 2.02/0.99  fof(f12,plain,(
% 2.02/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 2.02/0.99    inference(ennf_transformation,[],[f11])).
% 2.02/0.99  
% 2.02/0.99  fof(f25,plain,(
% 2.02/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f12])).
% 2.02/0.99  
% 2.02/0.99  fof(f36,plain,(
% 2.02/0.99    r1_tarski(sK4,sK2)),
% 2.02/0.99    inference(cnf_transformation,[],[f24])).
% 2.02/0.99  
% 2.02/0.99  fof(f37,plain,(
% 2.02/0.99    r1_tarski(sK4,sK3)),
% 2.02/0.99    inference(cnf_transformation,[],[f24])).
% 2.02/0.99  
% 2.02/0.99  fof(f4,axiom,(
% 2.02/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f13,plain,(
% 2.02/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.02/0.99    inference(ennf_transformation,[],[f4])).
% 2.02/0.99  
% 2.02/0.99  fof(f29,plain,(
% 2.02/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.02/0.99    inference(cnf_transformation,[],[f13])).
% 2.02/0.99  
% 2.02/0.99  fof(f27,plain,(
% 2.02/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.02/0.99    inference(cnf_transformation,[],[f18])).
% 2.02/0.99  
% 2.02/0.99  fof(f3,axiom,(
% 2.02/0.99    v1_xboole_0(k1_xboole_0)),
% 2.02/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/0.99  
% 2.02/0.99  fof(f28,plain,(
% 2.02/0.99    v1_xboole_0(k1_xboole_0)),
% 2.02/0.99    inference(cnf_transformation,[],[f3])).
% 2.02/0.99  
% 2.02/0.99  fof(f35,plain,(
% 2.02/0.99    ~v1_xboole_0(sK4)),
% 2.02/0.99    inference(cnf_transformation,[],[f24])).
% 2.02/0.99  
% 2.02/0.99  cnf(c_161,plain,
% 2.02/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.02/0.99      theory(equality) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_159,plain,
% 2.02/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.02/0.99      theory(equality) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_325,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_328,plain,
% 2.02/0.99      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 2.02/0.99      theory(equality) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_327,plain,( X0_40 = X0_40 ),theory(equality) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1219,plain,
% 2.02/0.99      ( X0_40 != X1_40 | X1_40 = X0_40 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_328,c_327]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_2,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.02/0.99      inference(cnf_transformation,[],[f26]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_323,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40) | k3_xboole_0(X0_40,X1_40) = k1_xboole_0 ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1451,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | X2_40 != k1_xboole_0
% 2.02/0.99      | k3_xboole_0(X0_40,X1_40) = X2_40 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_323,c_328]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1941,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | X2_40 = k3_xboole_0(X0_40,X1_40)
% 2.02/0.99      | X2_40 != k1_xboole_0 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1219,c_1451]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_330,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r1_xboole_0(X2_40,X3_40)
% 2.02/0.99      | X2_40 != X0_40
% 2.02/0.99      | X3_40 != X1_40 ),
% 2.02/0.99      theory(equality) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_2117,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r1_xboole_0(X2_40,X3_40)
% 2.02/0.99      | ~ r1_xboole_0(X4_40,k3_xboole_0(X0_40,X1_40))
% 2.02/0.99      | X2_40 != X4_40
% 2.02/0.99      | X3_40 != k1_xboole_0 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1941,c_330]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_8,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 2.02/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_318,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | ~ r2_hidden(X0_39,k3_xboole_0(X0_40,X1_40)) ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_6,plain,
% 2.02/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK0(X0,X1),X1) ),
% 2.02/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_320,plain,
% 2.02/0.99      ( r1_xboole_0(X0_40,X1_40) | r2_hidden(sK0(X0_40,X1_40),X1_40) ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1154,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r1_xboole_0(X2_40,k3_xboole_0(X0_40,X1_40)) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_318,c_320]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_3385,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r1_xboole_0(X2_40,X3_40)
% 2.02/0.99      | X2_40 != X4_40
% 2.02/0.99      | X3_40 != k1_xboole_0 ),
% 2.02/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2117,c_1154]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1834,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | X2_40 != X3_40
% 2.02/0.99      | X3_40 != k1_xboole_0
% 2.02/0.99      | k3_xboole_0(X0_40,X1_40) = X2_40 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1451,c_328]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_2538,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | ~ r1_xboole_0(X2_40,X3_40)
% 2.02/0.99      | X4_40 != k3_xboole_0(X2_40,X3_40)
% 2.02/0.99      | k3_xboole_0(X0_40,X1_40) = X4_40 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1834,c_323]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_2795,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | ~ r1_xboole_0(X2_40,X3_40)
% 2.02/0.99      | k3_xboole_0(X0_40,X1_40) = k3_xboole_0(X2_40,X3_40) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_2538,c_327]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1311,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r1_xboole_0(X2_40,X1_40)
% 2.02/0.99      | X2_40 != X0_40 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_330,c_327]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_2115,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r1_xboole_0(X2_40,X3_40)
% 2.02/0.99      | ~ r1_xboole_0(k3_xboole_0(X0_40,X1_40),X3_40)
% 2.02/0.99      | X2_40 != k1_xboole_0 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1941,c_1311]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_7,plain,
% 2.02/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 2.02/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_319,plain,
% 2.02/0.99      ( r1_xboole_0(X0_40,X1_40) | r2_hidden(sK0(X0_40,X1_40),X0_40) ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1150,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r1_xboole_0(k3_xboole_0(X0_40,X1_40),X2_40) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_318,c_319]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_2425,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r1_xboole_0(X2_40,X3_40)
% 2.02/0.99      | X2_40 != k1_xboole_0 ),
% 2.02/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2115,c_1150]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_329,plain,
% 2.02/0.99      ( ~ r2_hidden(X0_39,X0_40)
% 2.02/0.99      | r2_hidden(X1_39,X1_40)
% 2.02/0.99      | X1_40 != X0_40
% 2.02/0.99      | X1_39 != X0_39 ),
% 2.02/0.99      theory(equality) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_326,plain,( X0_39 = X0_39 ),theory(equality) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1230,plain,
% 2.02/0.99      ( ~ r2_hidden(X0_39,X0_40) | r2_hidden(X0_39,X1_40) | X1_40 != X0_40 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_329,c_326]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1956,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | ~ r2_hidden(X0_39,X2_40)
% 2.02/0.99      | r2_hidden(X0_39,k3_xboole_0(X0_40,X1_40))
% 2.02/0.99      | X2_40 != k1_xboole_0 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1230,c_1451]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_2250,plain,
% 2.02/0.99      ( ~ r2_hidden(X0_39,X2_40)
% 2.02/0.99      | ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | X2_40 != k1_xboole_0 ),
% 2.02/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1956,c_318]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_2251,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | ~ r2_hidden(X0_39,X2_40)
% 2.02/0.99      | X2_40 != k1_xboole_0 ),
% 2.02/0.99      inference(renaming,[status(thm)],[c_2250]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_2109,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | X2_40 = X3_40
% 2.02/0.99      | X3_40 != k3_xboole_0(X0_40,X1_40)
% 2.02/0.99      | X2_40 != k1_xboole_0 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1941,c_328]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1936,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40) | k1_xboole_0 = k3_xboole_0(X0_40,X1_40) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1219,c_323]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1989,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | X2_40 != k3_xboole_0(X0_40,X1_40)
% 2.02/0.99      | k1_xboole_0 = X2_40 ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1936,c_328]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_5,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 2.02/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_321,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | ~ r2_hidden(X0_39,X0_40)
% 2.02/0.99      | ~ r2_hidden(X0_39,X1_40) ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1530,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r1_xboole_0(X2_40,X1_40)
% 2.02/0.99      | ~ r2_hidden(sK0(X2_40,X1_40),X0_40) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_321,c_320]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1763,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X0_40) | r1_xboole_0(X1_40,X0_40) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1530,c_320]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1953,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r2_hidden(X0_39,k3_xboole_0(X0_40,X1_40))
% 2.02/0.99      | ~ r2_hidden(X0_39,k1_xboole_0) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1230,c_323]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_10,negated_conjecture,
% 2.02/0.99      ( r1_xboole_0(sK2,sK3) ),
% 2.02/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_316,negated_conjecture,
% 2.02/0.99      ( r1_xboole_0(sK2,sK3) ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_634,plain,
% 2.02/0.99      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 2.02/0.99      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_627,plain,
% 2.02/0.99      ( k3_xboole_0(X0_40,X1_40) = k1_xboole_0
% 2.02/0.99      | r1_xboole_0(X0_40,X1_40) != iProver_top ),
% 2.02/0.99      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1015,plain,
% 2.02/0.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 2.02/0.99      inference(superposition,[status(thm)],[c_634,c_627]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_632,plain,
% 2.02/0.99      ( r1_xboole_0(X0_40,X1_40) != iProver_top
% 2.02/0.99      | r2_hidden(X0_39,k3_xboole_0(X0_40,X1_40)) != iProver_top ),
% 2.02/0.99      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1278,plain,
% 2.02/0.99      ( r1_xboole_0(sK2,sK3) != iProver_top
% 2.02/0.99      | r2_hidden(X0_39,k1_xboole_0) != iProver_top ),
% 2.02/0.99      inference(superposition,[status(thm)],[c_1015,c_632]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1293,plain,
% 2.02/0.99      ( ~ r1_xboole_0(sK2,sK3) | ~ r2_hidden(X0_39,k1_xboole_0) ),
% 2.02/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1278]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1997,plain,
% 2.02/0.99      ( ~ r2_hidden(X0_39,k1_xboole_0) ),
% 2.02/0.99      inference(global_propositional_subsumption,
% 2.02/0.99                [status(thm)],
% 2.02/0.99                [c_1953,c_10,c_1293]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_2011,plain,
% 2.02/0.99      ( r1_xboole_0(X0_40,k1_xboole_0) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1997,c_320]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_2009,plain,
% 2.02/0.99      ( r1_xboole_0(k1_xboole_0,X0_40) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1997,c_319]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1528,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r1_xboole_0(X1_40,X2_40)
% 2.02/0.99      | ~ r2_hidden(sK0(X1_40,X2_40),X0_40) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_321,c_319]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1550,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X0_40) | r1_xboole_0(X0_40,X1_40) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_1528,c_319]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_9,plain,
% 2.02/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
% 2.02/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_317,plain,
% 2.02/0.99      ( r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | r2_hidden(sK1(X0_40,X1_40),k3_xboole_0(X0_40,X1_40)) ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1524,plain,
% 2.02/0.99      ( r1_xboole_0(X0_40,X1_40)
% 2.02/0.99      | ~ r1_xboole_0(X2_40,k3_xboole_0(X0_40,X1_40))
% 2.02/0.99      | ~ r2_hidden(sK1(X0_40,X1_40),X2_40) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_321,c_317]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_0,plain,
% 2.02/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.02/0.99      inference(cnf_transformation,[],[f25]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_12,negated_conjecture,
% 2.02/0.99      ( r1_tarski(sK4,sK2) ),
% 2.02/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_193,plain,
% 2.02/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | sK4 != X1 | sK2 != X2 ),
% 2.02/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_194,plain,
% 2.02/0.99      ( ~ r2_hidden(X0,sK4) | r2_hidden(X0,sK2) ),
% 2.02/0.99      inference(unflattening,[status(thm)],[c_193]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_313,plain,
% 2.02/0.99      ( ~ r2_hidden(X0_39,sK4) | r2_hidden(X0_39,sK2) ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_194]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_11,negated_conjecture,
% 2.02/0.99      ( r1_tarski(sK4,sK3) ),
% 2.02/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_181,plain,
% 2.02/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | sK4 != X1 | sK3 != X2 ),
% 2.02/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_182,plain,
% 2.02/0.99      ( ~ r2_hidden(X0,sK4) | r2_hidden(X0,sK3) ),
% 2.02/0.99      inference(unflattening,[status(thm)],[c_181]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_314,plain,
% 2.02/0.99      ( ~ r2_hidden(X0_39,sK4) | r2_hidden(X0_39,sK3) ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_182]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_635,plain,
% 2.02/0.99      ( r2_hidden(X0_39,sK4) != iProver_top
% 2.02/0.99      | r2_hidden(X0_39,sK3) = iProver_top ),
% 2.02/0.99      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_17,plain,
% 2.02/0.99      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 2.02/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_353,plain,
% 2.02/0.99      ( r2_hidden(X0_39,sK4) != iProver_top
% 2.02/0.99      | r2_hidden(X0_39,sK3) = iProver_top ),
% 2.02/0.99      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_356,plain,
% 2.02/0.99      ( r2_hidden(X0_39,sK4) != iProver_top
% 2.02/0.99      | r2_hidden(X0_39,sK2) = iProver_top ),
% 2.02/0.99      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_802,plain,
% 2.02/0.99      ( ~ r1_xboole_0(sK2,sK3)
% 2.02/0.99      | ~ r2_hidden(X0_39,sK3)
% 2.02/0.99      | ~ r2_hidden(X0_39,sK2) ),
% 2.02/0.99      inference(instantiation,[status(thm)],[c_321]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_803,plain,
% 2.02/0.99      ( r1_xboole_0(sK2,sK3) != iProver_top
% 2.02/0.99      | r2_hidden(X0_39,sK3) != iProver_top
% 2.02/0.99      | r2_hidden(X0_39,sK2) != iProver_top ),
% 2.02/0.99      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_881,plain,
% 2.02/0.99      ( r2_hidden(X0_39,sK4) != iProver_top ),
% 2.02/0.99      inference(global_propositional_subsumption,
% 2.02/0.99                [status(thm)],
% 2.02/0.99                [c_635,c_17,c_353,c_356,c_803]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_883,plain,
% 2.02/0.99      ( ~ r2_hidden(X0_39,sK4) ),
% 2.02/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_881]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_898,plain,
% 2.02/0.99      ( ~ r2_hidden(X0_39,sK4) ),
% 2.02/0.99      inference(global_propositional_subsumption,[status(thm)],[c_313,c_883]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_910,plain,
% 2.02/0.99      ( r1_xboole_0(sK4,X0_40) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_898,c_319]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_4,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.02/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_322,plain,
% 2.02/0.99      ( ~ r1_xboole_0(X0_40,X1_40) | r1_xboole_0(X1_40,X0_40) ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1022,plain,
% 2.02/0.99      ( r1_xboole_0(X0_40,sK4) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_910,c_322]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_790,plain,
% 2.02/0.99      ( r1_xboole_0(sK3,sK2) ),
% 2.02/0.99      inference(resolution,[status(thm)],[c_322,c_316]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_1,plain,
% 2.02/0.99      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.02/0.99      inference(cnf_transformation,[],[f27]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_324,plain,
% 2.02/0.99      ( r1_xboole_0(X0_40,X1_40) | k3_xboole_0(X0_40,X1_40) != k1_xboole_0 ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_3,plain,
% 2.02/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.02/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_13,negated_conjecture,
% 2.02/0.99      ( ~ v1_xboole_0(sK4) ),
% 2.02/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_176,plain,
% 2.02/0.99      ( sK4 != k1_xboole_0 ),
% 2.02/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 2.02/0.99  
% 2.02/0.99  cnf(c_315,plain,
% 2.02/0.99      ( sK4 != k1_xboole_0 ),
% 2.02/0.99      inference(subtyping,[status(esa)],[c_176]) ).
% 2.02/0.99  
% 2.02/0.99  
% 2.02/0.99  % SZS output end Saturation for theBenchmark.p
% 2.02/0.99  
% 2.02/0.99  ------                               Statistics
% 2.02/0.99  
% 2.02/0.99  ------ Selected
% 2.02/0.99  
% 2.02/0.99  total_time:                             0.139
% 2.02/0.99  
%------------------------------------------------------------------------------
