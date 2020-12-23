%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0592+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:40 EST 2020

% Result     : Theorem 0.72s
% Output     : CNFRefutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 113 expanded)
%              Number of clauses        :   36 (  43 expanded)
%              Number of leaves         :    9 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  143 ( 357 expanded)
%              Number of equality atoms :   87 ( 214 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f18,f15])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f8,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k1_relat_1(X1)
              & k1_xboole_0 = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k1_relat_1(X1)
                & k1_xboole_0 = k1_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
     => ( sK1 != X0
        & k1_xboole_0 = k1_relat_1(sK1)
        & k1_xboole_0 = k1_relat_1(X0)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & k1_xboole_0 = k1_relat_1(X1)
            & k1_xboole_0 = k1_relat_1(X0)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(sK0)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k1_relat_1(sK1)
    & k1_xboole_0 = k1_relat_1(sK0)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13,f12])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    o_0_0_xboole_0 = k1_relat_1(sK1) ),
    inference(definition_unfolding,[],[f22,f15])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    o_0_0_xboole_0 = k1_relat_1(sK0) ),
    inference(definition_unfolding,[],[f21,f15])).

fof(f23,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_286,plain,
    ( ~ v1_xboole_0(sK0)
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_119,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_263,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_275,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_276,plain,
    ( sK0 != sK0
    | sK0 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_118,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_262,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_249,plain,
    ( ~ v1_xboole_0(sK1)
    | o_0_0_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_243,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_241,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_242,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_244,plain,
    ( sK1 != sK1
    | sK1 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_238,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_239,plain,
    ( sK1 != o_0_0_xboole_0
    | sK0 = sK1
    | sK0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_59,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_60,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_59])).

cnf(c_202,plain,
    ( v1_xboole_0(k1_relat_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_4,negated_conjecture,
    ( o_0_0_xboole_0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_222,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_202,c_4])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_204,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_225,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_222,c_204])).

cnf(c_229,plain,
    ( v1_xboole_0(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_225])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_69,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_70,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_69])).

cnf(c_201,plain,
    ( v1_xboole_0(k1_relat_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_5,negated_conjecture,
    ( o_0_0_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_217,plain,
    ( v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_201,c_5])).

cnf(c_220,plain,
    ( v1_xboole_0(sK0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_217,c_204])).

cnf(c_227,plain,
    ( v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_220])).

cnf(c_3,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_286,c_276,c_262,c_249,c_243,c_244,c_239,c_229,c_227,c_3])).


%------------------------------------------------------------------------------
