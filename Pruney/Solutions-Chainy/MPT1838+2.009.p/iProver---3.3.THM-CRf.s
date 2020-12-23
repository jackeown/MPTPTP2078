%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:32 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 321 expanded)
%              Number of clauses        :   53 (  94 expanded)
%              Number of leaves         :   15 (  80 expanded)
%              Depth                    :   20
%              Number of atoms          :  250 (1298 expanded)
%              Number of equality atoms :  109 ( 373 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK3(X0)) = X0
        & m1_subset_1(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK3(X0)) = X0
            & m1_subset_1(sK3(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( sK5 != X0
        & r1_tarski(X0,sK5)
        & v1_zfmisc_1(sK5)
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK4 != X1
          & r1_tarski(sK4,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( sK4 != sK5
    & r1_tarski(sK4,sK5)
    & v1_zfmisc_1(sK5)
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f51,f50])).

fof(f81,plain,(
    v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK3(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_25,plain,
    ( m1_subset_1(sK3(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_383,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 != X1
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | sK3(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_25])).

cnf(c_384,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_28,negated_conjecture,
    ( v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_402,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_384,c_28])).

cnf(c_403,plain,
    ( v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_386,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_405,plain,
    ( k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_29,c_28,c_386])).

cnf(c_24,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_410,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK3(X0)) = X0
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_411,plain,
    ( v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_39,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v1_xboole_0(sK5)
    | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_413,plain,
    ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_29,c_28,c_39])).

cnf(c_1298,plain,
    ( k1_tarski(sK3(sK5)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_405,c_413])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1264,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1269,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1889,plain,
    ( k2_xboole_0(sK4,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_1264,c_1269])).

cnf(c_20,plain,
    ( X0 = X1
    | k2_xboole_0(X1,X0) != k1_tarski(X2)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1958,plain,
    ( k1_tarski(X0) != sK5
    | sK5 = sK4
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1889,c_20])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1557,plain,
    ( k2_xboole_0(sK5,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1298,c_21])).

cnf(c_1701,plain,
    ( k2_xboole_0(X0,sK5) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1557])).

cnf(c_1959,plain,
    ( sK5 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1889,c_1701])).

cnf(c_1966,plain,
    ( k1_tarski(X0) != sK5
    | sK5 = sK4
    | sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1958,c_1959])).

cnf(c_26,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_761,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1491,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_1544,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_760,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1545,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_2143,plain,
    ( k1_tarski(X0) != sK5
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1966,c_26,c_1544,c_1545])).

cnf(c_2148,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1298,c_2143])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1262,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2484,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2148,c_1262])).

cnf(c_1479,plain,
    ( k2_xboole_0(k1_tarski(X0),k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1978,plain,
    ( k2_xboole_0(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1650,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1651,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1650])).

cnf(c_1478,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_xboole_0)
    | k2_xboole_0(k1_tarski(X0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1572,plain,
    ( ~ r1_tarski(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0)
    | k2_xboole_0(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_1575,plain,
    ( k2_xboole_0(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1572])).

cnf(c_18,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1439,plain,
    ( r1_tarski(k1_tarski(sK0(X0)),X0)
    | ~ r2_hidden(sK0(X0),X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1571,plain,
    ( r1_tarski(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0)
    | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1439])).

cnf(c_1573,plain,
    ( r1_tarski(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1571])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2484,c_1978,c_1651,c_1575,c_1573])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 0.99/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.99/1.03  
% 0.99/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.99/1.03  
% 0.99/1.03  ------  iProver source info
% 0.99/1.03  
% 0.99/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.99/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.99/1.03  git: non_committed_changes: false
% 0.99/1.03  git: last_make_outside_of_git: false
% 0.99/1.03  
% 0.99/1.03  ------ 
% 0.99/1.03  
% 0.99/1.03  ------ Input Options
% 0.99/1.03  
% 0.99/1.03  --out_options                           all
% 0.99/1.03  --tptp_safe_out                         true
% 0.99/1.03  --problem_path                          ""
% 0.99/1.03  --include_path                          ""
% 0.99/1.03  --clausifier                            res/vclausify_rel
% 0.99/1.03  --clausifier_options                    --mode clausify
% 0.99/1.03  --stdin                                 false
% 0.99/1.03  --stats_out                             all
% 0.99/1.03  
% 0.99/1.03  ------ General Options
% 0.99/1.03  
% 0.99/1.03  --fof                                   false
% 0.99/1.03  --time_out_real                         305.
% 0.99/1.03  --time_out_virtual                      -1.
% 0.99/1.03  --symbol_type_check                     false
% 0.99/1.03  --clausify_out                          false
% 0.99/1.03  --sig_cnt_out                           false
% 0.99/1.03  --trig_cnt_out                          false
% 0.99/1.03  --trig_cnt_out_tolerance                1.
% 0.99/1.03  --trig_cnt_out_sk_spl                   false
% 0.99/1.03  --abstr_cl_out                          false
% 0.99/1.03  
% 0.99/1.03  ------ Global Options
% 0.99/1.03  
% 0.99/1.03  --schedule                              default
% 0.99/1.03  --add_important_lit                     false
% 0.99/1.03  --prop_solver_per_cl                    1000
% 0.99/1.03  --min_unsat_core                        false
% 0.99/1.03  --soft_assumptions                      false
% 0.99/1.03  --soft_lemma_size                       3
% 0.99/1.03  --prop_impl_unit_size                   0
% 0.99/1.03  --prop_impl_unit                        []
% 0.99/1.03  --share_sel_clauses                     true
% 0.99/1.03  --reset_solvers                         false
% 0.99/1.03  --bc_imp_inh                            [conj_cone]
% 0.99/1.03  --conj_cone_tolerance                   3.
% 0.99/1.03  --extra_neg_conj                        none
% 0.99/1.03  --large_theory_mode                     true
% 0.99/1.03  --prolific_symb_bound                   200
% 0.99/1.03  --lt_threshold                          2000
% 0.99/1.03  --clause_weak_htbl                      true
% 0.99/1.03  --gc_record_bc_elim                     false
% 0.99/1.03  
% 0.99/1.03  ------ Preprocessing Options
% 0.99/1.03  
% 0.99/1.03  --preprocessing_flag                    true
% 0.99/1.03  --time_out_prep_mult                    0.1
% 0.99/1.03  --splitting_mode                        input
% 0.99/1.03  --splitting_grd                         true
% 0.99/1.03  --splitting_cvd                         false
% 0.99/1.03  --splitting_cvd_svl                     false
% 0.99/1.03  --splitting_nvd                         32
% 0.99/1.03  --sub_typing                            true
% 0.99/1.03  --prep_gs_sim                           true
% 0.99/1.03  --prep_unflatten                        true
% 0.99/1.03  --prep_res_sim                          true
% 0.99/1.03  --prep_upred                            true
% 0.99/1.03  --prep_sem_filter                       exhaustive
% 0.99/1.03  --prep_sem_filter_out                   false
% 0.99/1.03  --pred_elim                             true
% 0.99/1.03  --res_sim_input                         true
% 0.99/1.03  --eq_ax_congr_red                       true
% 0.99/1.03  --pure_diseq_elim                       true
% 0.99/1.03  --brand_transform                       false
% 0.99/1.03  --non_eq_to_eq                          false
% 0.99/1.03  --prep_def_merge                        true
% 0.99/1.03  --prep_def_merge_prop_impl              false
% 0.99/1.03  --prep_def_merge_mbd                    true
% 0.99/1.03  --prep_def_merge_tr_red                 false
% 0.99/1.03  --prep_def_merge_tr_cl                  false
% 0.99/1.03  --smt_preprocessing                     true
% 0.99/1.03  --smt_ac_axioms                         fast
% 0.99/1.03  --preprocessed_out                      false
% 0.99/1.03  --preprocessed_stats                    false
% 0.99/1.03  
% 0.99/1.03  ------ Abstraction refinement Options
% 0.99/1.03  
% 0.99/1.03  --abstr_ref                             []
% 0.99/1.03  --abstr_ref_prep                        false
% 0.99/1.03  --abstr_ref_until_sat                   false
% 0.99/1.03  --abstr_ref_sig_restrict                funpre
% 0.99/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/1.03  --abstr_ref_under                       []
% 0.99/1.03  
% 0.99/1.03  ------ SAT Options
% 0.99/1.03  
% 0.99/1.03  --sat_mode                              false
% 0.99/1.03  --sat_fm_restart_options                ""
% 0.99/1.03  --sat_gr_def                            false
% 0.99/1.03  --sat_epr_types                         true
% 0.99/1.03  --sat_non_cyclic_types                  false
% 0.99/1.03  --sat_finite_models                     false
% 0.99/1.03  --sat_fm_lemmas                         false
% 0.99/1.03  --sat_fm_prep                           false
% 0.99/1.03  --sat_fm_uc_incr                        true
% 0.99/1.03  --sat_out_model                         small
% 0.99/1.03  --sat_out_clauses                       false
% 0.99/1.03  
% 0.99/1.03  ------ QBF Options
% 0.99/1.03  
% 0.99/1.03  --qbf_mode                              false
% 0.99/1.03  --qbf_elim_univ                         false
% 0.99/1.03  --qbf_dom_inst                          none
% 0.99/1.03  --qbf_dom_pre_inst                      false
% 0.99/1.03  --qbf_sk_in                             false
% 0.99/1.03  --qbf_pred_elim                         true
% 0.99/1.03  --qbf_split                             512
% 0.99/1.03  
% 0.99/1.03  ------ BMC1 Options
% 0.99/1.03  
% 0.99/1.03  --bmc1_incremental                      false
% 0.99/1.03  --bmc1_axioms                           reachable_all
% 0.99/1.03  --bmc1_min_bound                        0
% 0.99/1.03  --bmc1_max_bound                        -1
% 0.99/1.03  --bmc1_max_bound_default                -1
% 0.99/1.03  --bmc1_symbol_reachability              true
% 0.99/1.03  --bmc1_property_lemmas                  false
% 0.99/1.03  --bmc1_k_induction                      false
% 0.99/1.03  --bmc1_non_equiv_states                 false
% 0.99/1.03  --bmc1_deadlock                         false
% 0.99/1.03  --bmc1_ucm                              false
% 0.99/1.03  --bmc1_add_unsat_core                   none
% 0.99/1.03  --bmc1_unsat_core_children              false
% 0.99/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/1.03  --bmc1_out_stat                         full
% 0.99/1.03  --bmc1_ground_init                      false
% 0.99/1.03  --bmc1_pre_inst_next_state              false
% 0.99/1.03  --bmc1_pre_inst_state                   false
% 0.99/1.03  --bmc1_pre_inst_reach_state             false
% 0.99/1.03  --bmc1_out_unsat_core                   false
% 0.99/1.03  --bmc1_aig_witness_out                  false
% 0.99/1.03  --bmc1_verbose                          false
% 0.99/1.03  --bmc1_dump_clauses_tptp                false
% 0.99/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.99/1.03  --bmc1_dump_file                        -
% 0.99/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.99/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.99/1.03  --bmc1_ucm_extend_mode                  1
% 0.99/1.03  --bmc1_ucm_init_mode                    2
% 0.99/1.03  --bmc1_ucm_cone_mode                    none
% 0.99/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.99/1.03  --bmc1_ucm_relax_model                  4
% 0.99/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.99/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/1.03  --bmc1_ucm_layered_model                none
% 0.99/1.03  --bmc1_ucm_max_lemma_size               10
% 0.99/1.03  
% 0.99/1.03  ------ AIG Options
% 0.99/1.03  
% 0.99/1.03  --aig_mode                              false
% 0.99/1.03  
% 0.99/1.03  ------ Instantiation Options
% 0.99/1.03  
% 0.99/1.03  --instantiation_flag                    true
% 0.99/1.03  --inst_sos_flag                         false
% 0.99/1.03  --inst_sos_phase                        true
% 0.99/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/1.03  --inst_lit_sel_side                     num_symb
% 0.99/1.03  --inst_solver_per_active                1400
% 0.99/1.03  --inst_solver_calls_frac                1.
% 0.99/1.03  --inst_passive_queue_type               priority_queues
% 0.99/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/1.03  --inst_passive_queues_freq              [25;2]
% 0.99/1.03  --inst_dismatching                      true
% 0.99/1.03  --inst_eager_unprocessed_to_passive     true
% 0.99/1.03  --inst_prop_sim_given                   true
% 0.99/1.03  --inst_prop_sim_new                     false
% 0.99/1.03  --inst_subs_new                         false
% 0.99/1.03  --inst_eq_res_simp                      false
% 0.99/1.03  --inst_subs_given                       false
% 0.99/1.03  --inst_orphan_elimination               true
% 0.99/1.03  --inst_learning_loop_flag               true
% 0.99/1.03  --inst_learning_start                   3000
% 0.99/1.03  --inst_learning_factor                  2
% 0.99/1.03  --inst_start_prop_sim_after_learn       3
% 0.99/1.03  --inst_sel_renew                        solver
% 0.99/1.03  --inst_lit_activity_flag                true
% 0.99/1.03  --inst_restr_to_given                   false
% 0.99/1.03  --inst_activity_threshold               500
% 0.99/1.03  --inst_out_proof                        true
% 0.99/1.03  
% 0.99/1.03  ------ Resolution Options
% 0.99/1.03  
% 0.99/1.03  --resolution_flag                       true
% 0.99/1.03  --res_lit_sel                           adaptive
% 0.99/1.03  --res_lit_sel_side                      none
% 0.99/1.03  --res_ordering                          kbo
% 0.99/1.03  --res_to_prop_solver                    active
% 0.99/1.03  --res_prop_simpl_new                    false
% 0.99/1.03  --res_prop_simpl_given                  true
% 0.99/1.03  --res_passive_queue_type                priority_queues
% 0.99/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/1.03  --res_passive_queues_freq               [15;5]
% 0.99/1.03  --res_forward_subs                      full
% 0.99/1.03  --res_backward_subs                     full
% 0.99/1.03  --res_forward_subs_resolution           true
% 0.99/1.03  --res_backward_subs_resolution          true
% 0.99/1.03  --res_orphan_elimination                true
% 0.99/1.03  --res_time_limit                        2.
% 0.99/1.03  --res_out_proof                         true
% 0.99/1.03  
% 0.99/1.03  ------ Superposition Options
% 0.99/1.03  
% 0.99/1.03  --superposition_flag                    true
% 0.99/1.03  --sup_passive_queue_type                priority_queues
% 0.99/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.99/1.03  --demod_completeness_check              fast
% 0.99/1.03  --demod_use_ground                      true
% 0.99/1.03  --sup_to_prop_solver                    passive
% 0.99/1.03  --sup_prop_simpl_new                    true
% 0.99/1.03  --sup_prop_simpl_given                  true
% 0.99/1.03  --sup_fun_splitting                     false
% 0.99/1.03  --sup_smt_interval                      50000
% 0.99/1.03  
% 0.99/1.03  ------ Superposition Simplification Setup
% 0.99/1.03  
% 0.99/1.03  --sup_indices_passive                   []
% 0.99/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.03  --sup_full_bw                           [BwDemod]
% 0.99/1.03  --sup_immed_triv                        [TrivRules]
% 0.99/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.03  --sup_immed_bw_main                     []
% 0.99/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.03  
% 0.99/1.03  ------ Combination Options
% 0.99/1.03  
% 0.99/1.03  --comb_res_mult                         3
% 0.99/1.03  --comb_sup_mult                         2
% 0.99/1.03  --comb_inst_mult                        10
% 0.99/1.03  
% 0.99/1.03  ------ Debug Options
% 0.99/1.03  
% 0.99/1.03  --dbg_backtrace                         false
% 0.99/1.03  --dbg_dump_prop_clauses                 false
% 0.99/1.03  --dbg_dump_prop_clauses_file            -
% 0.99/1.03  --dbg_out_stat                          false
% 0.99/1.03  ------ Parsing...
% 0.99/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.99/1.03  
% 0.99/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.99/1.03  
% 0.99/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.99/1.03  
% 0.99/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.99/1.03  ------ Proving...
% 0.99/1.03  ------ Problem Properties 
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  clauses                                 27
% 0.99/1.03  conjectures                             4
% 0.99/1.03  EPR                                     6
% 0.99/1.03  Horn                                    22
% 0.99/1.03  unary                                   9
% 0.99/1.03  binary                                  11
% 0.99/1.03  lits                                    54
% 0.99/1.03  lits eq                                 14
% 0.99/1.03  fd_pure                                 0
% 0.99/1.03  fd_pseudo                               0
% 0.99/1.03  fd_cond                                 0
% 0.99/1.03  fd_pseudo_cond                          4
% 0.99/1.03  AC symbols                              0
% 0.99/1.03  
% 0.99/1.03  ------ Schedule dynamic 5 is on 
% 0.99/1.03  
% 0.99/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  ------ 
% 0.99/1.03  Current options:
% 0.99/1.03  ------ 
% 0.99/1.03  
% 0.99/1.03  ------ Input Options
% 0.99/1.03  
% 0.99/1.03  --out_options                           all
% 0.99/1.03  --tptp_safe_out                         true
% 0.99/1.03  --problem_path                          ""
% 0.99/1.03  --include_path                          ""
% 0.99/1.03  --clausifier                            res/vclausify_rel
% 0.99/1.03  --clausifier_options                    --mode clausify
% 0.99/1.03  --stdin                                 false
% 0.99/1.03  --stats_out                             all
% 0.99/1.03  
% 0.99/1.03  ------ General Options
% 0.99/1.03  
% 0.99/1.03  --fof                                   false
% 0.99/1.03  --time_out_real                         305.
% 0.99/1.03  --time_out_virtual                      -1.
% 0.99/1.03  --symbol_type_check                     false
% 0.99/1.03  --clausify_out                          false
% 0.99/1.03  --sig_cnt_out                           false
% 0.99/1.03  --trig_cnt_out                          false
% 0.99/1.03  --trig_cnt_out_tolerance                1.
% 0.99/1.03  --trig_cnt_out_sk_spl                   false
% 0.99/1.03  --abstr_cl_out                          false
% 0.99/1.03  
% 0.99/1.03  ------ Global Options
% 0.99/1.03  
% 0.99/1.03  --schedule                              default
% 0.99/1.03  --add_important_lit                     false
% 0.99/1.03  --prop_solver_per_cl                    1000
% 0.99/1.03  --min_unsat_core                        false
% 0.99/1.03  --soft_assumptions                      false
% 0.99/1.03  --soft_lemma_size                       3
% 0.99/1.03  --prop_impl_unit_size                   0
% 0.99/1.03  --prop_impl_unit                        []
% 0.99/1.03  --share_sel_clauses                     true
% 0.99/1.03  --reset_solvers                         false
% 0.99/1.03  --bc_imp_inh                            [conj_cone]
% 0.99/1.03  --conj_cone_tolerance                   3.
% 0.99/1.03  --extra_neg_conj                        none
% 0.99/1.03  --large_theory_mode                     true
% 0.99/1.03  --prolific_symb_bound                   200
% 0.99/1.03  --lt_threshold                          2000
% 0.99/1.03  --clause_weak_htbl                      true
% 0.99/1.03  --gc_record_bc_elim                     false
% 0.99/1.03  
% 0.99/1.03  ------ Preprocessing Options
% 0.99/1.03  
% 0.99/1.03  --preprocessing_flag                    true
% 0.99/1.03  --time_out_prep_mult                    0.1
% 0.99/1.03  --splitting_mode                        input
% 0.99/1.03  --splitting_grd                         true
% 0.99/1.03  --splitting_cvd                         false
% 0.99/1.03  --splitting_cvd_svl                     false
% 0.99/1.03  --splitting_nvd                         32
% 0.99/1.03  --sub_typing                            true
% 0.99/1.03  --prep_gs_sim                           true
% 0.99/1.03  --prep_unflatten                        true
% 0.99/1.03  --prep_res_sim                          true
% 0.99/1.03  --prep_upred                            true
% 0.99/1.03  --prep_sem_filter                       exhaustive
% 0.99/1.03  --prep_sem_filter_out                   false
% 0.99/1.03  --pred_elim                             true
% 0.99/1.03  --res_sim_input                         true
% 0.99/1.03  --eq_ax_congr_red                       true
% 0.99/1.03  --pure_diseq_elim                       true
% 0.99/1.03  --brand_transform                       false
% 0.99/1.03  --non_eq_to_eq                          false
% 0.99/1.03  --prep_def_merge                        true
% 0.99/1.03  --prep_def_merge_prop_impl              false
% 0.99/1.03  --prep_def_merge_mbd                    true
% 0.99/1.03  --prep_def_merge_tr_red                 false
% 0.99/1.03  --prep_def_merge_tr_cl                  false
% 0.99/1.03  --smt_preprocessing                     true
% 0.99/1.03  --smt_ac_axioms                         fast
% 0.99/1.03  --preprocessed_out                      false
% 0.99/1.03  --preprocessed_stats                    false
% 0.99/1.03  
% 0.99/1.03  ------ Abstraction refinement Options
% 0.99/1.03  
% 0.99/1.03  --abstr_ref                             []
% 0.99/1.03  --abstr_ref_prep                        false
% 0.99/1.03  --abstr_ref_until_sat                   false
% 0.99/1.03  --abstr_ref_sig_restrict                funpre
% 0.99/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/1.03  --abstr_ref_under                       []
% 0.99/1.03  
% 0.99/1.03  ------ SAT Options
% 0.99/1.03  
% 0.99/1.03  --sat_mode                              false
% 0.99/1.03  --sat_fm_restart_options                ""
% 0.99/1.03  --sat_gr_def                            false
% 0.99/1.03  --sat_epr_types                         true
% 0.99/1.03  --sat_non_cyclic_types                  false
% 0.99/1.03  --sat_finite_models                     false
% 0.99/1.03  --sat_fm_lemmas                         false
% 0.99/1.03  --sat_fm_prep                           false
% 0.99/1.03  --sat_fm_uc_incr                        true
% 0.99/1.03  --sat_out_model                         small
% 0.99/1.03  --sat_out_clauses                       false
% 0.99/1.03  
% 0.99/1.03  ------ QBF Options
% 0.99/1.03  
% 0.99/1.03  --qbf_mode                              false
% 0.99/1.03  --qbf_elim_univ                         false
% 0.99/1.03  --qbf_dom_inst                          none
% 0.99/1.03  --qbf_dom_pre_inst                      false
% 0.99/1.03  --qbf_sk_in                             false
% 0.99/1.03  --qbf_pred_elim                         true
% 0.99/1.03  --qbf_split                             512
% 0.99/1.03  
% 0.99/1.03  ------ BMC1 Options
% 0.99/1.03  
% 0.99/1.03  --bmc1_incremental                      false
% 0.99/1.03  --bmc1_axioms                           reachable_all
% 0.99/1.03  --bmc1_min_bound                        0
% 0.99/1.03  --bmc1_max_bound                        -1
% 0.99/1.03  --bmc1_max_bound_default                -1
% 0.99/1.03  --bmc1_symbol_reachability              true
% 0.99/1.03  --bmc1_property_lemmas                  false
% 0.99/1.03  --bmc1_k_induction                      false
% 0.99/1.03  --bmc1_non_equiv_states                 false
% 0.99/1.03  --bmc1_deadlock                         false
% 0.99/1.03  --bmc1_ucm                              false
% 0.99/1.03  --bmc1_add_unsat_core                   none
% 0.99/1.03  --bmc1_unsat_core_children              false
% 0.99/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/1.03  --bmc1_out_stat                         full
% 0.99/1.03  --bmc1_ground_init                      false
% 0.99/1.03  --bmc1_pre_inst_next_state              false
% 0.99/1.03  --bmc1_pre_inst_state                   false
% 0.99/1.03  --bmc1_pre_inst_reach_state             false
% 0.99/1.03  --bmc1_out_unsat_core                   false
% 0.99/1.03  --bmc1_aig_witness_out                  false
% 0.99/1.03  --bmc1_verbose                          false
% 0.99/1.03  --bmc1_dump_clauses_tptp                false
% 0.99/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.99/1.03  --bmc1_dump_file                        -
% 0.99/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.99/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.99/1.03  --bmc1_ucm_extend_mode                  1
% 0.99/1.03  --bmc1_ucm_init_mode                    2
% 0.99/1.03  --bmc1_ucm_cone_mode                    none
% 0.99/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.99/1.03  --bmc1_ucm_relax_model                  4
% 0.99/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.99/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/1.03  --bmc1_ucm_layered_model                none
% 0.99/1.03  --bmc1_ucm_max_lemma_size               10
% 0.99/1.03  
% 0.99/1.03  ------ AIG Options
% 0.99/1.03  
% 0.99/1.03  --aig_mode                              false
% 0.99/1.03  
% 0.99/1.03  ------ Instantiation Options
% 0.99/1.03  
% 0.99/1.03  --instantiation_flag                    true
% 0.99/1.03  --inst_sos_flag                         false
% 0.99/1.03  --inst_sos_phase                        true
% 0.99/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/1.03  --inst_lit_sel_side                     none
% 0.99/1.03  --inst_solver_per_active                1400
% 0.99/1.03  --inst_solver_calls_frac                1.
% 0.99/1.03  --inst_passive_queue_type               priority_queues
% 0.99/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/1.03  --inst_passive_queues_freq              [25;2]
% 0.99/1.03  --inst_dismatching                      true
% 0.99/1.03  --inst_eager_unprocessed_to_passive     true
% 0.99/1.03  --inst_prop_sim_given                   true
% 0.99/1.03  --inst_prop_sim_new                     false
% 0.99/1.03  --inst_subs_new                         false
% 0.99/1.03  --inst_eq_res_simp                      false
% 0.99/1.03  --inst_subs_given                       false
% 0.99/1.03  --inst_orphan_elimination               true
% 0.99/1.03  --inst_learning_loop_flag               true
% 0.99/1.03  --inst_learning_start                   3000
% 0.99/1.03  --inst_learning_factor                  2
% 0.99/1.03  --inst_start_prop_sim_after_learn       3
% 0.99/1.03  --inst_sel_renew                        solver
% 0.99/1.03  --inst_lit_activity_flag                true
% 0.99/1.03  --inst_restr_to_given                   false
% 0.99/1.03  --inst_activity_threshold               500
% 0.99/1.03  --inst_out_proof                        true
% 0.99/1.03  
% 0.99/1.03  ------ Resolution Options
% 0.99/1.03  
% 0.99/1.03  --resolution_flag                       false
% 0.99/1.03  --res_lit_sel                           adaptive
% 0.99/1.03  --res_lit_sel_side                      none
% 0.99/1.03  --res_ordering                          kbo
% 0.99/1.03  --res_to_prop_solver                    active
% 0.99/1.03  --res_prop_simpl_new                    false
% 0.99/1.03  --res_prop_simpl_given                  true
% 0.99/1.03  --res_passive_queue_type                priority_queues
% 0.99/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/1.03  --res_passive_queues_freq               [15;5]
% 0.99/1.03  --res_forward_subs                      full
% 0.99/1.03  --res_backward_subs                     full
% 0.99/1.03  --res_forward_subs_resolution           true
% 0.99/1.03  --res_backward_subs_resolution          true
% 0.99/1.03  --res_orphan_elimination                true
% 0.99/1.03  --res_time_limit                        2.
% 0.99/1.03  --res_out_proof                         true
% 0.99/1.03  
% 0.99/1.03  ------ Superposition Options
% 0.99/1.03  
% 0.99/1.03  --superposition_flag                    true
% 0.99/1.03  --sup_passive_queue_type                priority_queues
% 0.99/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.99/1.03  --demod_completeness_check              fast
% 0.99/1.03  --demod_use_ground                      true
% 0.99/1.03  --sup_to_prop_solver                    passive
% 0.99/1.03  --sup_prop_simpl_new                    true
% 0.99/1.03  --sup_prop_simpl_given                  true
% 0.99/1.03  --sup_fun_splitting                     false
% 0.99/1.03  --sup_smt_interval                      50000
% 0.99/1.03  
% 0.99/1.03  ------ Superposition Simplification Setup
% 0.99/1.03  
% 0.99/1.03  --sup_indices_passive                   []
% 0.99/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.03  --sup_full_bw                           [BwDemod]
% 0.99/1.03  --sup_immed_triv                        [TrivRules]
% 0.99/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.03  --sup_immed_bw_main                     []
% 0.99/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.03  
% 0.99/1.03  ------ Combination Options
% 0.99/1.03  
% 0.99/1.03  --comb_res_mult                         3
% 0.99/1.03  --comb_sup_mult                         2
% 0.99/1.03  --comb_inst_mult                        10
% 0.99/1.03  
% 0.99/1.03  ------ Debug Options
% 0.99/1.03  
% 0.99/1.03  --dbg_backtrace                         false
% 0.99/1.03  --dbg_dump_prop_clauses                 false
% 0.99/1.03  --dbg_dump_prop_clauses_file            -
% 0.99/1.03  --dbg_out_stat                          false
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  ------ Proving...
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  % SZS status Theorem for theBenchmark.p
% 0.99/1.03  
% 0.99/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.99/1.03  
% 0.99/1.03  fof(f14,axiom,(
% 0.99/1.03    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.99/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f27,plain,(
% 0.99/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.99/1.03    inference(ennf_transformation,[],[f14])).
% 0.99/1.03  
% 0.99/1.03  fof(f28,plain,(
% 0.99/1.03    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.99/1.03    inference(flattening,[],[f27])).
% 0.99/1.03  
% 0.99/1.03  fof(f75,plain,(
% 0.99/1.03    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f28])).
% 0.99/1.03  
% 0.99/1.03  fof(f15,axiom,(
% 0.99/1.03    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.99/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f29,plain,(
% 0.99/1.03    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.99/1.03    inference(ennf_transformation,[],[f15])).
% 0.99/1.03  
% 0.99/1.03  fof(f46,plain,(
% 0.99/1.03    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.99/1.03    inference(nnf_transformation,[],[f29])).
% 0.99/1.03  
% 0.99/1.03  fof(f47,plain,(
% 0.99/1.03    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.99/1.03    inference(rectify,[],[f46])).
% 0.99/1.03  
% 0.99/1.03  fof(f48,plain,(
% 0.99/1.03    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)))),
% 0.99/1.03    introduced(choice_axiom,[])).
% 0.99/1.03  
% 0.99/1.03  fof(f49,plain,(
% 0.99/1.03    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.99/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 0.99/1.03  
% 0.99/1.03  fof(f76,plain,(
% 0.99/1.03    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f49])).
% 0.99/1.03  
% 0.99/1.03  fof(f16,conjecture,(
% 0.99/1.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.99/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f17,negated_conjecture,(
% 0.99/1.03    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.99/1.03    inference(negated_conjecture,[],[f16])).
% 0.99/1.03  
% 0.99/1.03  fof(f30,plain,(
% 0.99/1.03    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.99/1.03    inference(ennf_transformation,[],[f17])).
% 0.99/1.03  
% 0.99/1.03  fof(f31,plain,(
% 0.99/1.03    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.99/1.03    inference(flattening,[],[f30])).
% 0.99/1.03  
% 0.99/1.03  fof(f51,plain,(
% 0.99/1.03    ( ! [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK5 != X0 & r1_tarski(X0,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5))) )),
% 0.99/1.03    introduced(choice_axiom,[])).
% 0.99/1.03  
% 0.99/1.03  fof(f50,plain,(
% 0.99/1.03    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK4 != X1 & r1_tarski(sK4,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK4))),
% 0.99/1.03    introduced(choice_axiom,[])).
% 0.99/1.03  
% 0.99/1.03  fof(f52,plain,(
% 0.99/1.03    (sK4 != sK5 & r1_tarski(sK4,sK5) & v1_zfmisc_1(sK5) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)),
% 0.99/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f31,f51,f50])).
% 0.99/1.03  
% 0.99/1.03  fof(f81,plain,(
% 0.99/1.03    v1_zfmisc_1(sK5)),
% 0.99/1.03    inference(cnf_transformation,[],[f52])).
% 0.99/1.03  
% 0.99/1.03  fof(f80,plain,(
% 0.99/1.03    ~v1_xboole_0(sK5)),
% 0.99/1.03    inference(cnf_transformation,[],[f52])).
% 0.99/1.03  
% 0.99/1.03  fof(f77,plain,(
% 0.99/1.03    ( ! [X0] : (k6_domain_1(X0,sK3(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f49])).
% 0.99/1.03  
% 0.99/1.03  fof(f82,plain,(
% 0.99/1.03    r1_tarski(sK4,sK5)),
% 0.99/1.03    inference(cnf_transformation,[],[f52])).
% 0.99/1.03  
% 0.99/1.03  fof(f6,axiom,(
% 0.99/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.99/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f21,plain,(
% 0.99/1.03    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.99/1.03    inference(ennf_transformation,[],[f6])).
% 0.99/1.03  
% 0.99/1.03  fof(f66,plain,(
% 0.99/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f21])).
% 0.99/1.03  
% 0.99/1.03  fof(f12,axiom,(
% 0.99/1.03    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.99/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f26,plain,(
% 0.99/1.03    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 0.99/1.03    inference(ennf_transformation,[],[f12])).
% 0.99/1.03  
% 0.99/1.03  fof(f73,plain,(
% 0.99/1.03    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f26])).
% 0.99/1.03  
% 0.99/1.03  fof(f1,axiom,(
% 0.99/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.99/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f53,plain,(
% 0.99/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f1])).
% 0.99/1.03  
% 0.99/1.03  fof(f13,axiom,(
% 0.99/1.03    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.99/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f74,plain,(
% 0.99/1.03    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.99/1.03    inference(cnf_transformation,[],[f13])).
% 0.99/1.03  
% 0.99/1.03  fof(f83,plain,(
% 0.99/1.03    sK4 != sK5),
% 0.99/1.03    inference(cnf_transformation,[],[f52])).
% 0.99/1.03  
% 0.99/1.03  fof(f79,plain,(
% 0.99/1.03    ~v1_xboole_0(sK4)),
% 0.99/1.03    inference(cnf_transformation,[],[f52])).
% 0.99/1.03  
% 0.99/1.03  fof(f2,axiom,(
% 0.99/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.99/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f32,plain,(
% 0.99/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.99/1.03    inference(nnf_transformation,[],[f2])).
% 0.99/1.03  
% 0.99/1.03  fof(f33,plain,(
% 0.99/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.99/1.03    inference(rectify,[],[f32])).
% 0.99/1.03  
% 0.99/1.03  fof(f34,plain,(
% 0.99/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 0.99/1.03    introduced(choice_axiom,[])).
% 0.99/1.03  
% 0.99/1.03  fof(f35,plain,(
% 0.99/1.03    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.99/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 0.99/1.04  
% 0.99/1.04  fof(f55,plain,(
% 0.99/1.04    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 0.99/1.04    inference(cnf_transformation,[],[f35])).
% 0.99/1.04  
% 0.99/1.04  fof(f11,axiom,(
% 0.99/1.04    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.99/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/1.04  
% 0.99/1.04  fof(f45,plain,(
% 0.99/1.04    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.99/1.04    inference(nnf_transformation,[],[f11])).
% 0.99/1.04  
% 0.99/1.04  fof(f72,plain,(
% 0.99/1.04    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.99/1.04    inference(cnf_transformation,[],[f45])).
% 0.99/1.04  
% 0.99/1.04  cnf(c_22,plain,
% 0.99/1.04      ( ~ m1_subset_1(X0,X1)
% 0.99/1.04      | v1_xboole_0(X1)
% 0.99/1.04      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 0.99/1.04      inference(cnf_transformation,[],[f75]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_25,plain,
% 0.99/1.04      ( m1_subset_1(sK3(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 0.99/1.04      inference(cnf_transformation,[],[f76]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_383,plain,
% 0.99/1.04      ( ~ v1_zfmisc_1(X0)
% 0.99/1.04      | v1_xboole_0(X1)
% 0.99/1.04      | v1_xboole_0(X0)
% 0.99/1.04      | X0 != X1
% 0.99/1.04      | k6_domain_1(X1,X2) = k1_tarski(X2)
% 0.99/1.04      | sK3(X0) != X2 ),
% 0.99/1.04      inference(resolution_lifted,[status(thm)],[c_22,c_25]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_384,plain,
% 0.99/1.04      ( ~ v1_zfmisc_1(X0)
% 0.99/1.04      | v1_xboole_0(X0)
% 0.99/1.04      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0)) ),
% 0.99/1.04      inference(unflattening,[status(thm)],[c_383]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_28,negated_conjecture,
% 0.99/1.04      ( v1_zfmisc_1(sK5) ),
% 0.99/1.04      inference(cnf_transformation,[],[f81]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_402,plain,
% 0.99/1.04      ( v1_xboole_0(X0)
% 0.99/1.04      | k6_domain_1(X0,sK3(X0)) = k1_tarski(sK3(X0))
% 0.99/1.04      | sK5 != X0 ),
% 0.99/1.04      inference(resolution_lifted,[status(thm)],[c_384,c_28]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_403,plain,
% 0.99/1.04      ( v1_xboole_0(sK5)
% 0.99/1.04      | k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
% 0.99/1.04      inference(unflattening,[status(thm)],[c_402]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_29,negated_conjecture,
% 0.99/1.04      ( ~ v1_xboole_0(sK5) ),
% 0.99/1.04      inference(cnf_transformation,[],[f80]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_386,plain,
% 0.99/1.04      ( ~ v1_zfmisc_1(sK5)
% 0.99/1.04      | v1_xboole_0(sK5)
% 0.99/1.04      | k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_384]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_405,plain,
% 0.99/1.04      ( k6_domain_1(sK5,sK3(sK5)) = k1_tarski(sK3(sK5)) ),
% 0.99/1.04      inference(global_propositional_subsumption,
% 0.99/1.04                [status(thm)],
% 0.99/1.04                [c_403,c_29,c_28,c_386]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_24,plain,
% 0.99/1.04      ( ~ v1_zfmisc_1(X0)
% 0.99/1.04      | v1_xboole_0(X0)
% 0.99/1.04      | k6_domain_1(X0,sK3(X0)) = X0 ),
% 0.99/1.04      inference(cnf_transformation,[],[f77]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_410,plain,
% 0.99/1.04      ( v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = X0 | sK5 != X0 ),
% 0.99/1.04      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_411,plain,
% 0.99/1.04      ( v1_xboole_0(sK5) | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 0.99/1.04      inference(unflattening,[status(thm)],[c_410]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_39,plain,
% 0.99/1.04      ( ~ v1_zfmisc_1(sK5)
% 0.99/1.04      | v1_xboole_0(sK5)
% 0.99/1.04      | k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_24]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_413,plain,
% 0.99/1.04      ( k6_domain_1(sK5,sK3(sK5)) = sK5 ),
% 0.99/1.04      inference(global_propositional_subsumption,
% 0.99/1.04                [status(thm)],
% 0.99/1.04                [c_411,c_29,c_28,c_39]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1298,plain,
% 0.99/1.04      ( k1_tarski(sK3(sK5)) = sK5 ),
% 0.99/1.04      inference(light_normalisation,[status(thm)],[c_405,c_413]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_27,negated_conjecture,
% 0.99/1.04      ( r1_tarski(sK4,sK5) ),
% 0.99/1.04      inference(cnf_transformation,[],[f82]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1264,plain,
% 0.99/1.04      ( r1_tarski(sK4,sK5) = iProver_top ),
% 0.99/1.04      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_13,plain,
% 0.99/1.04      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 0.99/1.04      inference(cnf_transformation,[],[f66]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1269,plain,
% 0.99/1.04      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 0.99/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1889,plain,
% 0.99/1.04      ( k2_xboole_0(sK4,sK5) = sK5 ),
% 0.99/1.04      inference(superposition,[status(thm)],[c_1264,c_1269]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_20,plain,
% 0.99/1.04      ( X0 = X1
% 0.99/1.04      | k2_xboole_0(X1,X0) != k1_tarski(X2)
% 0.99/1.04      | k1_xboole_0 = X0
% 0.99/1.04      | k1_xboole_0 = X1 ),
% 0.99/1.04      inference(cnf_transformation,[],[f73]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1958,plain,
% 0.99/1.04      ( k1_tarski(X0) != sK5
% 0.99/1.04      | sK5 = sK4
% 0.99/1.04      | sK5 = k1_xboole_0
% 0.99/1.04      | sK4 = k1_xboole_0 ),
% 0.99/1.04      inference(superposition,[status(thm)],[c_1889,c_20]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_0,plain,
% 0.99/1.04      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 0.99/1.04      inference(cnf_transformation,[],[f53]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_21,plain,
% 0.99/1.04      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 0.99/1.04      inference(cnf_transformation,[],[f74]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1557,plain,
% 0.99/1.04      ( k2_xboole_0(sK5,X0) != k1_xboole_0 ),
% 0.99/1.04      inference(superposition,[status(thm)],[c_1298,c_21]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1701,plain,
% 0.99/1.04      ( k2_xboole_0(X0,sK5) != k1_xboole_0 ),
% 0.99/1.04      inference(superposition,[status(thm)],[c_0,c_1557]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1959,plain,
% 0.99/1.04      ( sK5 != k1_xboole_0 ),
% 0.99/1.04      inference(superposition,[status(thm)],[c_1889,c_1701]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1966,plain,
% 0.99/1.04      ( k1_tarski(X0) != sK5 | sK5 = sK4 | sK4 = k1_xboole_0 ),
% 0.99/1.04      inference(forward_subsumption_resolution,
% 0.99/1.04                [status(thm)],
% 0.99/1.04                [c_1958,c_1959]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_26,negated_conjecture,
% 0.99/1.04      ( sK4 != sK5 ),
% 0.99/1.04      inference(cnf_transformation,[],[f83]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_761,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1491,plain,
% 0.99/1.04      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_761]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1544,plain,
% 0.99/1.04      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_1491]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_760,plain,( X0 = X0 ),theory(equality) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1545,plain,
% 0.99/1.04      ( sK4 = sK4 ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_760]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_2143,plain,
% 0.99/1.04      ( k1_tarski(X0) != sK5 | sK4 = k1_xboole_0 ),
% 0.99/1.04      inference(global_propositional_subsumption,
% 0.99/1.04                [status(thm)],
% 0.99/1.04                [c_1966,c_26,c_1544,c_1545]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_2148,plain,
% 0.99/1.04      ( sK4 = k1_xboole_0 ),
% 0.99/1.04      inference(superposition,[status(thm)],[c_1298,c_2143]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_30,negated_conjecture,
% 0.99/1.04      ( ~ v1_xboole_0(sK4) ),
% 0.99/1.04      inference(cnf_transformation,[],[f79]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1262,plain,
% 0.99/1.04      ( v1_xboole_0(sK4) != iProver_top ),
% 0.99/1.04      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_2484,plain,
% 0.99/1.04      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 0.99/1.04      inference(demodulation,[status(thm)],[c_2148,c_1262]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1479,plain,
% 0.99/1.04      ( k2_xboole_0(k1_tarski(X0),k1_xboole_0) != k1_xboole_0 ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_21]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1978,plain,
% 0.99/1.04      ( k2_xboole_0(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0) != k1_xboole_0 ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_1479]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1,plain,
% 0.99/1.04      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 0.99/1.04      inference(cnf_transformation,[],[f55]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1650,plain,
% 0.99/1.04      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 0.99/1.04      | v1_xboole_0(k1_xboole_0) ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1651,plain,
% 0.99/1.04      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0) = iProver_top
% 0.99/1.04      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 0.99/1.04      inference(predicate_to_equality,[status(thm)],[c_1650]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1478,plain,
% 0.99/1.04      ( ~ r1_tarski(k1_tarski(X0),k1_xboole_0)
% 0.99/1.04      | k2_xboole_0(k1_tarski(X0),k1_xboole_0) = k1_xboole_0 ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_13]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1572,plain,
% 0.99/1.04      ( ~ r1_tarski(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0)
% 0.99/1.04      | k2_xboole_0(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_1478]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1575,plain,
% 0.99/1.04      ( k2_xboole_0(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0) = k1_xboole_0
% 0.99/1.04      | r1_tarski(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0) != iProver_top ),
% 0.99/1.04      inference(predicate_to_equality,[status(thm)],[c_1572]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_18,plain,
% 0.99/1.04      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 0.99/1.04      inference(cnf_transformation,[],[f72]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1439,plain,
% 0.99/1.04      ( r1_tarski(k1_tarski(sK0(X0)),X0) | ~ r2_hidden(sK0(X0),X0) ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_18]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1571,plain,
% 0.99/1.04      ( r1_tarski(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0)
% 0.99/1.04      | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
% 0.99/1.04      inference(instantiation,[status(thm)],[c_1439]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(c_1573,plain,
% 0.99/1.04      ( r1_tarski(k1_tarski(sK0(k1_xboole_0)),k1_xboole_0) = iProver_top
% 0.99/1.04      | r2_hidden(sK0(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 0.99/1.04      inference(predicate_to_equality,[status(thm)],[c_1571]) ).
% 0.99/1.04  
% 0.99/1.04  cnf(contradiction,plain,
% 0.99/1.04      ( $false ),
% 0.99/1.04      inference(minisat,
% 0.99/1.04                [status(thm)],
% 0.99/1.04                [c_2484,c_1978,c_1651,c_1575,c_1573]) ).
% 0.99/1.04  
% 0.99/1.04  
% 0.99/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.99/1.04  
% 0.99/1.04  ------                               Statistics
% 0.99/1.04  
% 0.99/1.04  ------ General
% 0.99/1.04  
% 0.99/1.04  abstr_ref_over_cycles:                  0
% 0.99/1.04  abstr_ref_under_cycles:                 0
% 0.99/1.04  gc_basic_clause_elim:                   0
% 0.99/1.04  forced_gc_time:                         0
% 0.99/1.04  parsing_time:                           0.025
% 0.99/1.04  unif_index_cands_time:                  0.
% 0.99/1.04  unif_index_add_time:                    0.
% 0.99/1.04  orderings_time:                         0.
% 0.99/1.04  out_proof_time:                         0.023
% 0.99/1.04  total_time:                             0.144
% 0.99/1.04  num_of_symbols:                         48
% 0.99/1.04  num_of_terms:                           1942
% 0.99/1.04  
% 0.99/1.04  ------ Preprocessing
% 0.99/1.04  
% 0.99/1.04  num_of_splits:                          0
% 0.99/1.04  num_of_split_atoms:                     0
% 0.99/1.04  num_of_reused_defs:                     0
% 0.99/1.04  num_eq_ax_congr_red:                    33
% 0.99/1.04  num_of_sem_filtered_clauses:            1
% 0.99/1.04  num_of_subtypes:                        0
% 0.99/1.04  monotx_restored_types:                  0
% 0.99/1.04  sat_num_of_epr_types:                   0
% 0.99/1.04  sat_num_of_non_cyclic_types:            0
% 0.99/1.04  sat_guarded_non_collapsed_types:        0
% 0.99/1.04  num_pure_diseq_elim:                    0
% 0.99/1.04  simp_replaced_by:                       0
% 0.99/1.04  res_preprocessed:                       131
% 0.99/1.04  prep_upred:                             0
% 0.99/1.04  prep_unflattend:                        18
% 0.99/1.04  smt_new_axioms:                         0
% 0.99/1.04  pred_elim_cands:                        3
% 0.99/1.04  pred_elim:                              3
% 0.99/1.04  pred_elim_cl:                           4
% 0.99/1.04  pred_elim_cycles:                       5
% 0.99/1.04  merged_defs:                            8
% 0.99/1.04  merged_defs_ncl:                        0
% 0.99/1.04  bin_hyper_res:                          8
% 0.99/1.04  prep_cycles:                            4
% 0.99/1.04  pred_elim_time:                         0.004
% 0.99/1.04  splitting_time:                         0.
% 0.99/1.04  sem_filter_time:                        0.
% 0.99/1.04  monotx_time:                            0.001
% 0.99/1.04  subtype_inf_time:                       0.
% 0.99/1.04  
% 0.99/1.04  ------ Problem properties
% 0.99/1.04  
% 0.99/1.04  clauses:                                27
% 0.99/1.04  conjectures:                            4
% 0.99/1.04  epr:                                    6
% 0.99/1.04  horn:                                   22
% 0.99/1.04  ground:                                 6
% 0.99/1.04  unary:                                  9
% 0.99/1.04  binary:                                 11
% 0.99/1.04  lits:                                   54
% 0.99/1.04  lits_eq:                                14
% 0.99/1.04  fd_pure:                                0
% 0.99/1.04  fd_pseudo:                              0
% 0.99/1.04  fd_cond:                                0
% 0.99/1.04  fd_pseudo_cond:                         4
% 0.99/1.04  ac_symbols:                             0
% 0.99/1.04  
% 0.99/1.04  ------ Propositional Solver
% 0.99/1.04  
% 0.99/1.04  prop_solver_calls:                      26
% 0.99/1.04  prop_fast_solver_calls:                 634
% 0.99/1.04  smt_solver_calls:                       0
% 0.99/1.04  smt_fast_solver_calls:                  0
% 0.99/1.04  prop_num_of_clauses:                    736
% 0.99/1.04  prop_preprocess_simplified:             4126
% 0.99/1.04  prop_fo_subsumed:                       3
% 0.99/1.04  prop_solver_time:                       0.
% 0.99/1.04  smt_solver_time:                        0.
% 0.99/1.04  smt_fast_solver_time:                   0.
% 0.99/1.04  prop_fast_solver_time:                  0.
% 0.99/1.04  prop_unsat_core_time:                   0.
% 0.99/1.04  
% 0.99/1.04  ------ QBF
% 0.99/1.04  
% 0.99/1.04  qbf_q_res:                              0
% 0.99/1.04  qbf_num_tautologies:                    0
% 0.99/1.04  qbf_prep_cycles:                        0
% 0.99/1.04  
% 0.99/1.04  ------ BMC1
% 0.99/1.04  
% 0.99/1.04  bmc1_current_bound:                     -1
% 0.99/1.04  bmc1_last_solved_bound:                 -1
% 0.99/1.04  bmc1_unsat_core_size:                   -1
% 0.99/1.04  bmc1_unsat_core_parents_size:           -1
% 0.99/1.04  bmc1_merge_next_fun:                    0
% 0.99/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.99/1.04  
% 0.99/1.04  ------ Instantiation
% 0.99/1.04  
% 0.99/1.04  inst_num_of_clauses:                    212
% 0.99/1.04  inst_num_in_passive:                    50
% 0.99/1.04  inst_num_in_active:                     102
% 0.99/1.04  inst_num_in_unprocessed:                60
% 0.99/1.04  inst_num_of_loops:                      140
% 0.99/1.04  inst_num_of_learning_restarts:          0
% 0.99/1.04  inst_num_moves_active_passive:          36
% 0.99/1.04  inst_lit_activity:                      0
% 0.99/1.04  inst_lit_activity_moves:                0
% 0.99/1.04  inst_num_tautologies:                   0
% 0.99/1.04  inst_num_prop_implied:                  0
% 0.99/1.04  inst_num_existing_simplified:           0
% 0.99/1.04  inst_num_eq_res_simplified:             0
% 0.99/1.04  inst_num_child_elim:                    0
% 0.99/1.04  inst_num_of_dismatching_blockings:      64
% 0.99/1.04  inst_num_of_non_proper_insts:           187
% 0.99/1.04  inst_num_of_duplicates:                 0
% 0.99/1.04  inst_inst_num_from_inst_to_res:         0
% 0.99/1.04  inst_dismatching_checking_time:         0.
% 0.99/1.04  
% 0.99/1.04  ------ Resolution
% 0.99/1.04  
% 0.99/1.04  res_num_of_clauses:                     0
% 0.99/1.04  res_num_in_passive:                     0
% 0.99/1.04  res_num_in_active:                      0
% 0.99/1.04  res_num_of_loops:                       135
% 0.99/1.04  res_forward_subset_subsumed:            9
% 0.99/1.04  res_backward_subset_subsumed:           0
% 0.99/1.04  res_forward_subsumed:                   0
% 0.99/1.04  res_backward_subsumed:                  0
% 0.99/1.04  res_forward_subsumption_resolution:     0
% 0.99/1.04  res_backward_subsumption_resolution:    0
% 0.99/1.04  res_clause_to_clause_subsumption:       71
% 0.99/1.04  res_orphan_elimination:                 0
% 0.99/1.04  res_tautology_del:                      26
% 0.99/1.04  res_num_eq_res_simplified:              0
% 0.99/1.04  res_num_sel_changes:                    0
% 0.99/1.04  res_moves_from_active_to_pass:          0
% 0.99/1.04  
% 0.99/1.04  ------ Superposition
% 0.99/1.04  
% 0.99/1.04  sup_time_total:                         0.
% 0.99/1.04  sup_time_generating:                    0.
% 0.99/1.04  sup_time_sim_full:                      0.
% 0.99/1.04  sup_time_sim_immed:                     0.
% 0.99/1.04  
% 0.99/1.04  sup_num_of_clauses:                     44
% 0.99/1.04  sup_num_in_active:                      21
% 0.99/1.04  sup_num_in_passive:                     23
% 0.99/1.04  sup_num_of_loops:                       26
% 0.99/1.04  sup_fw_superposition:                   25
% 0.99/1.04  sup_bw_superposition:                   13
% 0.99/1.04  sup_immediate_simplified:               1
% 0.99/1.04  sup_given_eliminated:                   0
% 0.99/1.04  comparisons_done:                       0
% 0.99/1.04  comparisons_avoided:                    0
% 0.99/1.04  
% 0.99/1.04  ------ Simplifications
% 0.99/1.04  
% 0.99/1.04  
% 0.99/1.04  sim_fw_subset_subsumed:                 0
% 0.99/1.04  sim_bw_subset_subsumed:                 0
% 0.99/1.04  sim_fw_subsumed:                        0
% 0.99/1.04  sim_bw_subsumed:                        0
% 0.99/1.04  sim_fw_subsumption_res:                 1
% 0.99/1.04  sim_bw_subsumption_res:                 0
% 0.99/1.04  sim_tautology_del:                      1
% 0.99/1.04  sim_eq_tautology_del:                   2
% 0.99/1.04  sim_eq_res_simp:                        0
% 0.99/1.04  sim_fw_demodulated:                     0
% 0.99/1.04  sim_bw_demodulated:                     5
% 0.99/1.04  sim_light_normalised:                   1
% 0.99/1.04  sim_joinable_taut:                      0
% 0.99/1.04  sim_joinable_simp:                      0
% 0.99/1.04  sim_ac_normalised:                      0
% 0.99/1.04  sim_smt_subsumption:                    0
% 0.99/1.04  
%------------------------------------------------------------------------------
