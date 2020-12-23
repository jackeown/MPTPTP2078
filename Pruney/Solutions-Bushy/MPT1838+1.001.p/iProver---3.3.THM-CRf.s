%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1838+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:36 EST 2020

% Result     : Theorem 1.00s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 274 expanded)
%              Number of clauses        :   40 (  76 expanded)
%              Number of leaves         :   10 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  199 (1181 expanded)
%              Number of equality atoms :   89 ( 331 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( sK2 != X0
        & r1_tarski(X0,sK2)
        & v1_zfmisc_1(sK2)
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK1 != X1
          & r1_tarski(sK1,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( sK1 != sK2
    & r1_tarski(sK1,sK2)
    & v1_zfmisc_1(sK2)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f19,f18])).

fof(f31,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK0(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f16])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_148,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | X1 != X0
    | k6_domain_1(X0,X2) = k1_tarski(X2)
    | sK0(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_2])).

cnf(c_149,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0)
    | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0)) ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_10,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_169,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_149,c_10])).

cnf(c_170,plain,
    ( v1_xboole_0(sK2)
    | k6_domain_1(sK2,sK0(sK2)) = k1_tarski(sK0(sK2)) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_11,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_151,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_zfmisc_1(sK2)
    | k6_domain_1(sK2,sK0(sK2)) = k1_tarski(sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_172,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = k1_tarski(sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_170,c_11,c_10,c_151])).

cnf(c_233,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = k1_tarski(sK0(sK2)) ),
    inference(subtyping,[status(esa)],[c_172])).

cnf(c_1,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0)
    | k6_domain_1(X0,sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_177,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_178,plain,
    ( v1_xboole_0(sK2)
    | k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_177])).

cnf(c_34,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_zfmisc_1(sK2)
    | k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_180,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_178,c_11,c_10,c_34])).

cnf(c_232,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(subtyping,[status(esa)],[c_180])).

cnf(c_323,plain,
    ( k1_tarski(sK0(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_233,c_232])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_133,plain,
    ( k1_tarski(X0) = X1
    | k1_tarski(X0) != sK2
    | sK1 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_134,plain,
    ( k1_tarski(X0) != sK2
    | k1_tarski(X0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_234,plain,
    ( k1_tarski(X0_39) != sK2
    | k1_tarski(X0_39) = sK1
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_134])).

cnf(c_395,plain,
    ( k1_tarski(sK0(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_323,c_234])).

cnf(c_396,plain,
    ( sK2 = sK1
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_395,c_323])).

cnf(c_8,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_237,negated_conjecture,
    ( sK1 != sK2 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_242,plain,
    ( X0_38 != X1_38
    | X2_38 != X1_38
    | X2_38 = X0_38 ),
    theory(equality)).

cnf(c_348,plain,
    ( sK2 != X0_38
    | sK1 != X0_38
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_349,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_240,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_350,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_432,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_237,c_349,c_350])).

cnf(c_12,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_235,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_312,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_436,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_432,c_312])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_29,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_436,c_29])).


%------------------------------------------------------------------------------
