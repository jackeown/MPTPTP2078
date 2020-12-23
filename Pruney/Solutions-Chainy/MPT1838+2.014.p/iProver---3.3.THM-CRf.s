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
% DateTime   : Thu Dec  3 12:24:33 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 180 expanded)
%              Number of clauses        :   51 (  60 expanded)
%              Number of leaves         :   15 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  265 ( 658 expanded)
%              Number of equality atoms :   87 ( 162 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( sK4 != X0
        & r1_tarski(X0,sK4)
        & v1_zfmisc_1(sK4)
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK3 != X1
          & r1_tarski(sK3,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( sK3 != sK4
    & r1_tarski(sK3,sK4)
    & v1_zfmisc_1(sK4)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f47,f46])).

fof(f78,plain,(
    v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,plain,
    ( m1_subset_1(sK2(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_333,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 != X1
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | sK2(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_25])).

cnf(c_334,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0)) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_28,negated_conjecture,
    ( v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_352,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_334,c_28])).

cnf(c_353,plain,
    ( v1_xboole_0(sK4)
    | k6_domain_1(sK4,sK2(sK4)) = k1_tarski(sK2(sK4)) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_355,plain,
    ( k6_domain_1(sK4,sK2(sK4)) = k1_tarski(sK2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_29])).

cnf(c_24,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_360,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK2(X0)) = X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_361,plain,
    ( v1_xboole_0(sK4)
    | k6_domain_1(sK4,sK2(sK4)) = sK4 ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_363,plain,
    ( k6_domain_1(sK4,sK2(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_29])).

cnf(c_1058,plain,
    ( k1_tarski(sK2(sK4)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_355,c_363])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1021,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1026,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3305,plain,
    ( k2_xboole_0(sK3,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_1021,c_1026])).

cnf(c_19,plain,
    ( X0 = X1
    | k2_xboole_0(X1,X0) != k1_tarski(X2)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3478,plain,
    ( k1_tarski(X0) != sK4
    | sK4 = sK3
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3305,c_19])).

cnf(c_15,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_58,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_382,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_29])).

cnf(c_383,plain,
    ( r2_hidden(sK0(sK4),sK4) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_389,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_30])).

cnf(c_390,plain,
    ( r2_hidden(sK0(sK3),sK3) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_578,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_598,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1190,plain,
    ( ~ r1_tarski(sK4,sK0(sK4))
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1193,plain,
    ( ~ r1_tarski(sK3,sK0(sK3))
    | ~ r2_hidden(sK0(sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1287,plain,
    ( ~ r1_tarski(X0,sK0(sK4))
    | ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1289,plain,
    ( r1_tarski(sK4,sK0(sK4))
    | ~ r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_1300,plain,
    ( ~ r1_tarski(X0,sK0(sK3))
    | ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1302,plain,
    ( r1_tarski(sK3,sK0(sK3))
    | ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_584,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1593,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X2)
    | X2 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_1595,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK4 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_1620,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_1622,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_2171,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4267,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4343,plain,
    ( k1_tarski(X0) != sK4
    | sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3478,c_58,c_383,c_390,c_598,c_1190,c_1193,c_1289,c_1302,c_1595,c_1622,c_2171,c_4267])).

cnf(c_4348,plain,
    ( sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1058,c_4343])).

cnf(c_26,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4857,plain,
    ( sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_4348,c_26])).

cnf(c_4858,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_4857])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.73/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.02  
% 2.73/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/1.02  
% 2.73/1.02  ------  iProver source info
% 2.73/1.02  
% 2.73/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.73/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/1.02  git: non_committed_changes: false
% 2.73/1.02  git: last_make_outside_of_git: false
% 2.73/1.02  
% 2.73/1.02  ------ 
% 2.73/1.02  
% 2.73/1.02  ------ Input Options
% 2.73/1.02  
% 2.73/1.02  --out_options                           all
% 2.73/1.02  --tptp_safe_out                         true
% 2.73/1.02  --problem_path                          ""
% 2.73/1.02  --include_path                          ""
% 2.73/1.02  --clausifier                            res/vclausify_rel
% 2.73/1.02  --clausifier_options                    --mode clausify
% 2.73/1.02  --stdin                                 false
% 2.73/1.02  --stats_out                             all
% 2.73/1.02  
% 2.73/1.02  ------ General Options
% 2.73/1.02  
% 2.73/1.02  --fof                                   false
% 2.73/1.02  --time_out_real                         305.
% 2.73/1.02  --time_out_virtual                      -1.
% 2.73/1.02  --symbol_type_check                     false
% 2.73/1.02  --clausify_out                          false
% 2.73/1.02  --sig_cnt_out                           false
% 2.73/1.02  --trig_cnt_out                          false
% 2.73/1.02  --trig_cnt_out_tolerance                1.
% 2.73/1.02  --trig_cnt_out_sk_spl                   false
% 2.73/1.02  --abstr_cl_out                          false
% 2.73/1.02  
% 2.73/1.02  ------ Global Options
% 2.73/1.02  
% 2.73/1.02  --schedule                              default
% 2.73/1.02  --add_important_lit                     false
% 2.73/1.02  --prop_solver_per_cl                    1000
% 2.73/1.02  --min_unsat_core                        false
% 2.73/1.02  --soft_assumptions                      false
% 2.73/1.02  --soft_lemma_size                       3
% 2.73/1.02  --prop_impl_unit_size                   0
% 2.73/1.02  --prop_impl_unit                        []
% 2.73/1.02  --share_sel_clauses                     true
% 2.73/1.02  --reset_solvers                         false
% 2.73/1.02  --bc_imp_inh                            [conj_cone]
% 2.73/1.02  --conj_cone_tolerance                   3.
% 2.73/1.02  --extra_neg_conj                        none
% 2.73/1.02  --large_theory_mode                     true
% 2.73/1.02  --prolific_symb_bound                   200
% 2.73/1.02  --lt_threshold                          2000
% 2.73/1.02  --clause_weak_htbl                      true
% 2.73/1.02  --gc_record_bc_elim                     false
% 2.73/1.02  
% 2.73/1.02  ------ Preprocessing Options
% 2.73/1.02  
% 2.73/1.02  --preprocessing_flag                    true
% 2.73/1.02  --time_out_prep_mult                    0.1
% 2.73/1.02  --splitting_mode                        input
% 2.73/1.02  --splitting_grd                         true
% 2.73/1.02  --splitting_cvd                         false
% 2.73/1.02  --splitting_cvd_svl                     false
% 2.73/1.02  --splitting_nvd                         32
% 2.73/1.02  --sub_typing                            true
% 2.73/1.02  --prep_gs_sim                           true
% 2.73/1.02  --prep_unflatten                        true
% 2.73/1.02  --prep_res_sim                          true
% 2.73/1.02  --prep_upred                            true
% 2.73/1.02  --prep_sem_filter                       exhaustive
% 2.73/1.02  --prep_sem_filter_out                   false
% 2.73/1.02  --pred_elim                             true
% 2.73/1.02  --res_sim_input                         true
% 2.73/1.02  --eq_ax_congr_red                       true
% 2.73/1.02  --pure_diseq_elim                       true
% 2.73/1.02  --brand_transform                       false
% 2.73/1.02  --non_eq_to_eq                          false
% 2.73/1.02  --prep_def_merge                        true
% 2.73/1.02  --prep_def_merge_prop_impl              false
% 2.73/1.02  --prep_def_merge_mbd                    true
% 2.73/1.02  --prep_def_merge_tr_red                 false
% 2.73/1.02  --prep_def_merge_tr_cl                  false
% 2.73/1.02  --smt_preprocessing                     true
% 2.73/1.02  --smt_ac_axioms                         fast
% 2.73/1.02  --preprocessed_out                      false
% 2.73/1.02  --preprocessed_stats                    false
% 2.73/1.02  
% 2.73/1.02  ------ Abstraction refinement Options
% 2.73/1.02  
% 2.73/1.02  --abstr_ref                             []
% 2.73/1.02  --abstr_ref_prep                        false
% 2.73/1.02  --abstr_ref_until_sat                   false
% 2.73/1.02  --abstr_ref_sig_restrict                funpre
% 2.73/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.02  --abstr_ref_under                       []
% 2.73/1.02  
% 2.73/1.02  ------ SAT Options
% 2.73/1.02  
% 2.73/1.02  --sat_mode                              false
% 2.73/1.02  --sat_fm_restart_options                ""
% 2.73/1.02  --sat_gr_def                            false
% 2.73/1.02  --sat_epr_types                         true
% 2.73/1.02  --sat_non_cyclic_types                  false
% 2.73/1.02  --sat_finite_models                     false
% 2.73/1.02  --sat_fm_lemmas                         false
% 2.73/1.02  --sat_fm_prep                           false
% 2.73/1.02  --sat_fm_uc_incr                        true
% 2.73/1.02  --sat_out_model                         small
% 2.73/1.02  --sat_out_clauses                       false
% 2.73/1.02  
% 2.73/1.02  ------ QBF Options
% 2.73/1.02  
% 2.73/1.02  --qbf_mode                              false
% 2.73/1.02  --qbf_elim_univ                         false
% 2.73/1.02  --qbf_dom_inst                          none
% 2.73/1.02  --qbf_dom_pre_inst                      false
% 2.73/1.02  --qbf_sk_in                             false
% 2.73/1.02  --qbf_pred_elim                         true
% 2.73/1.02  --qbf_split                             512
% 2.73/1.02  
% 2.73/1.02  ------ BMC1 Options
% 2.73/1.02  
% 2.73/1.02  --bmc1_incremental                      false
% 2.73/1.02  --bmc1_axioms                           reachable_all
% 2.73/1.02  --bmc1_min_bound                        0
% 2.73/1.02  --bmc1_max_bound                        -1
% 2.73/1.02  --bmc1_max_bound_default                -1
% 2.73/1.02  --bmc1_symbol_reachability              true
% 2.73/1.02  --bmc1_property_lemmas                  false
% 2.73/1.02  --bmc1_k_induction                      false
% 2.73/1.02  --bmc1_non_equiv_states                 false
% 2.73/1.02  --bmc1_deadlock                         false
% 2.73/1.02  --bmc1_ucm                              false
% 2.73/1.02  --bmc1_add_unsat_core                   none
% 2.73/1.02  --bmc1_unsat_core_children              false
% 2.73/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.02  --bmc1_out_stat                         full
% 2.73/1.02  --bmc1_ground_init                      false
% 2.73/1.02  --bmc1_pre_inst_next_state              false
% 2.73/1.02  --bmc1_pre_inst_state                   false
% 2.73/1.02  --bmc1_pre_inst_reach_state             false
% 2.73/1.02  --bmc1_out_unsat_core                   false
% 2.73/1.02  --bmc1_aig_witness_out                  false
% 2.73/1.02  --bmc1_verbose                          false
% 2.73/1.02  --bmc1_dump_clauses_tptp                false
% 2.73/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.02  --bmc1_dump_file                        -
% 2.73/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.02  --bmc1_ucm_extend_mode                  1
% 2.73/1.02  --bmc1_ucm_init_mode                    2
% 2.73/1.02  --bmc1_ucm_cone_mode                    none
% 2.73/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.02  --bmc1_ucm_relax_model                  4
% 2.73/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.02  --bmc1_ucm_layered_model                none
% 2.73/1.02  --bmc1_ucm_max_lemma_size               10
% 2.73/1.02  
% 2.73/1.02  ------ AIG Options
% 2.73/1.02  
% 2.73/1.02  --aig_mode                              false
% 2.73/1.02  
% 2.73/1.02  ------ Instantiation Options
% 2.73/1.02  
% 2.73/1.02  --instantiation_flag                    true
% 2.73/1.02  --inst_sos_flag                         false
% 2.73/1.02  --inst_sos_phase                        true
% 2.73/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.02  --inst_lit_sel_side                     num_symb
% 2.73/1.02  --inst_solver_per_active                1400
% 2.73/1.02  --inst_solver_calls_frac                1.
% 2.73/1.02  --inst_passive_queue_type               priority_queues
% 2.73/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.02  --inst_passive_queues_freq              [25;2]
% 2.73/1.02  --inst_dismatching                      true
% 2.73/1.02  --inst_eager_unprocessed_to_passive     true
% 2.73/1.02  --inst_prop_sim_given                   true
% 2.73/1.02  --inst_prop_sim_new                     false
% 2.73/1.02  --inst_subs_new                         false
% 2.73/1.02  --inst_eq_res_simp                      false
% 2.73/1.02  --inst_subs_given                       false
% 2.73/1.02  --inst_orphan_elimination               true
% 2.73/1.02  --inst_learning_loop_flag               true
% 2.73/1.02  --inst_learning_start                   3000
% 2.73/1.02  --inst_learning_factor                  2
% 2.73/1.02  --inst_start_prop_sim_after_learn       3
% 2.73/1.02  --inst_sel_renew                        solver
% 2.73/1.02  --inst_lit_activity_flag                true
% 2.73/1.02  --inst_restr_to_given                   false
% 2.73/1.02  --inst_activity_threshold               500
% 2.73/1.02  --inst_out_proof                        true
% 2.73/1.02  
% 2.73/1.02  ------ Resolution Options
% 2.73/1.02  
% 2.73/1.02  --resolution_flag                       true
% 2.73/1.02  --res_lit_sel                           adaptive
% 2.73/1.02  --res_lit_sel_side                      none
% 2.73/1.02  --res_ordering                          kbo
% 2.73/1.02  --res_to_prop_solver                    active
% 2.73/1.02  --res_prop_simpl_new                    false
% 2.73/1.02  --res_prop_simpl_given                  true
% 2.73/1.02  --res_passive_queue_type                priority_queues
% 2.73/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.02  --res_passive_queues_freq               [15;5]
% 2.73/1.02  --res_forward_subs                      full
% 2.73/1.02  --res_backward_subs                     full
% 2.73/1.02  --res_forward_subs_resolution           true
% 2.73/1.02  --res_backward_subs_resolution          true
% 2.73/1.02  --res_orphan_elimination                true
% 2.73/1.02  --res_time_limit                        2.
% 2.73/1.02  --res_out_proof                         true
% 2.73/1.02  
% 2.73/1.02  ------ Superposition Options
% 2.73/1.02  
% 2.73/1.02  --superposition_flag                    true
% 2.73/1.02  --sup_passive_queue_type                priority_queues
% 2.73/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.02  --demod_completeness_check              fast
% 2.73/1.02  --demod_use_ground                      true
% 2.73/1.02  --sup_to_prop_solver                    passive
% 2.73/1.02  --sup_prop_simpl_new                    true
% 2.73/1.02  --sup_prop_simpl_given                  true
% 2.73/1.02  --sup_fun_splitting                     false
% 2.73/1.02  --sup_smt_interval                      50000
% 2.73/1.02  
% 2.73/1.02  ------ Superposition Simplification Setup
% 2.73/1.02  
% 2.73/1.02  --sup_indices_passive                   []
% 2.73/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.02  --sup_full_bw                           [BwDemod]
% 2.73/1.02  --sup_immed_triv                        [TrivRules]
% 2.73/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.02  --sup_immed_bw_main                     []
% 2.73/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.02  
% 2.73/1.02  ------ Combination Options
% 2.73/1.02  
% 2.73/1.02  --comb_res_mult                         3
% 2.73/1.02  --comb_sup_mult                         2
% 2.73/1.02  --comb_inst_mult                        10
% 2.73/1.02  
% 2.73/1.02  ------ Debug Options
% 2.73/1.02  
% 2.73/1.02  --dbg_backtrace                         false
% 2.73/1.02  --dbg_dump_prop_clauses                 false
% 2.73/1.02  --dbg_dump_prop_clauses_file            -
% 2.73/1.02  --dbg_out_stat                          false
% 2.73/1.02  ------ Parsing...
% 2.73/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/1.02  
% 2.73/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.73/1.02  
% 2.73/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/1.02  
% 2.73/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/1.02  ------ Proving...
% 2.73/1.02  ------ Problem Properties 
% 2.73/1.02  
% 2.73/1.02  
% 2.73/1.02  clauses                                 27
% 2.73/1.02  conjectures                             2
% 2.73/1.02  EPR                                     5
% 2.73/1.02  Horn                                    24
% 2.73/1.02  unary                                   13
% 2.73/1.02  binary                                  8
% 2.73/1.02  lits                                    49
% 2.73/1.02  lits eq                                 18
% 2.73/1.02  fd_pure                                 0
% 2.73/1.02  fd_pseudo                               0
% 2.73/1.02  fd_cond                                 0
% 2.73/1.02  fd_pseudo_cond                          4
% 2.73/1.02  AC symbols                              0
% 2.73/1.02  
% 2.73/1.02  ------ Schedule dynamic 5 is on 
% 2.73/1.02  
% 2.73/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/1.02  
% 2.73/1.02  
% 2.73/1.02  ------ 
% 2.73/1.02  Current options:
% 2.73/1.02  ------ 
% 2.73/1.02  
% 2.73/1.02  ------ Input Options
% 2.73/1.02  
% 2.73/1.02  --out_options                           all
% 2.73/1.02  --tptp_safe_out                         true
% 2.73/1.02  --problem_path                          ""
% 2.73/1.02  --include_path                          ""
% 2.73/1.02  --clausifier                            res/vclausify_rel
% 2.73/1.02  --clausifier_options                    --mode clausify
% 2.73/1.02  --stdin                                 false
% 2.73/1.02  --stats_out                             all
% 2.73/1.02  
% 2.73/1.02  ------ General Options
% 2.73/1.02  
% 2.73/1.02  --fof                                   false
% 2.73/1.02  --time_out_real                         305.
% 2.73/1.02  --time_out_virtual                      -1.
% 2.73/1.02  --symbol_type_check                     false
% 2.73/1.02  --clausify_out                          false
% 2.73/1.02  --sig_cnt_out                           false
% 2.73/1.02  --trig_cnt_out                          false
% 2.73/1.02  --trig_cnt_out_tolerance                1.
% 2.73/1.02  --trig_cnt_out_sk_spl                   false
% 2.73/1.02  --abstr_cl_out                          false
% 2.73/1.02  
% 2.73/1.02  ------ Global Options
% 2.73/1.02  
% 2.73/1.02  --schedule                              default
% 2.73/1.02  --add_important_lit                     false
% 2.73/1.02  --prop_solver_per_cl                    1000
% 2.73/1.02  --min_unsat_core                        false
% 2.73/1.02  --soft_assumptions                      false
% 2.73/1.02  --soft_lemma_size                       3
% 2.73/1.02  --prop_impl_unit_size                   0
% 2.73/1.02  --prop_impl_unit                        []
% 2.73/1.02  --share_sel_clauses                     true
% 2.73/1.02  --reset_solvers                         false
% 2.73/1.02  --bc_imp_inh                            [conj_cone]
% 2.73/1.02  --conj_cone_tolerance                   3.
% 2.73/1.02  --extra_neg_conj                        none
% 2.73/1.02  --large_theory_mode                     true
% 2.73/1.02  --prolific_symb_bound                   200
% 2.73/1.02  --lt_threshold                          2000
% 2.73/1.02  --clause_weak_htbl                      true
% 2.73/1.02  --gc_record_bc_elim                     false
% 2.73/1.02  
% 2.73/1.02  ------ Preprocessing Options
% 2.73/1.02  
% 2.73/1.02  --preprocessing_flag                    true
% 2.73/1.02  --time_out_prep_mult                    0.1
% 2.73/1.02  --splitting_mode                        input
% 2.73/1.02  --splitting_grd                         true
% 2.73/1.02  --splitting_cvd                         false
% 2.73/1.02  --splitting_cvd_svl                     false
% 2.73/1.02  --splitting_nvd                         32
% 2.73/1.02  --sub_typing                            true
% 2.73/1.02  --prep_gs_sim                           true
% 2.73/1.02  --prep_unflatten                        true
% 2.73/1.02  --prep_res_sim                          true
% 2.73/1.02  --prep_upred                            true
% 2.73/1.02  --prep_sem_filter                       exhaustive
% 2.73/1.02  --prep_sem_filter_out                   false
% 2.73/1.02  --pred_elim                             true
% 2.73/1.02  --res_sim_input                         true
% 2.73/1.02  --eq_ax_congr_red                       true
% 2.73/1.02  --pure_diseq_elim                       true
% 2.73/1.02  --brand_transform                       false
% 2.73/1.02  --non_eq_to_eq                          false
% 2.73/1.02  --prep_def_merge                        true
% 2.73/1.02  --prep_def_merge_prop_impl              false
% 2.73/1.02  --prep_def_merge_mbd                    true
% 2.73/1.02  --prep_def_merge_tr_red                 false
% 2.73/1.02  --prep_def_merge_tr_cl                  false
% 2.73/1.02  --smt_preprocessing                     true
% 2.73/1.02  --smt_ac_axioms                         fast
% 2.73/1.02  --preprocessed_out                      false
% 2.73/1.02  --preprocessed_stats                    false
% 2.73/1.02  
% 2.73/1.02  ------ Abstraction refinement Options
% 2.73/1.02  
% 2.73/1.02  --abstr_ref                             []
% 2.73/1.02  --abstr_ref_prep                        false
% 2.73/1.02  --abstr_ref_until_sat                   false
% 2.73/1.02  --abstr_ref_sig_restrict                funpre
% 2.73/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.02  --abstr_ref_under                       []
% 2.73/1.02  
% 2.73/1.02  ------ SAT Options
% 2.73/1.02  
% 2.73/1.02  --sat_mode                              false
% 2.73/1.02  --sat_fm_restart_options                ""
% 2.73/1.02  --sat_gr_def                            false
% 2.73/1.02  --sat_epr_types                         true
% 2.73/1.02  --sat_non_cyclic_types                  false
% 2.73/1.02  --sat_finite_models                     false
% 2.73/1.02  --sat_fm_lemmas                         false
% 2.73/1.02  --sat_fm_prep                           false
% 2.73/1.02  --sat_fm_uc_incr                        true
% 2.73/1.02  --sat_out_model                         small
% 2.73/1.02  --sat_out_clauses                       false
% 2.73/1.02  
% 2.73/1.02  ------ QBF Options
% 2.73/1.02  
% 2.73/1.02  --qbf_mode                              false
% 2.73/1.02  --qbf_elim_univ                         false
% 2.73/1.02  --qbf_dom_inst                          none
% 2.73/1.02  --qbf_dom_pre_inst                      false
% 2.73/1.02  --qbf_sk_in                             false
% 2.73/1.02  --qbf_pred_elim                         true
% 2.73/1.02  --qbf_split                             512
% 2.73/1.02  
% 2.73/1.02  ------ BMC1 Options
% 2.73/1.02  
% 2.73/1.02  --bmc1_incremental                      false
% 2.73/1.02  --bmc1_axioms                           reachable_all
% 2.73/1.02  --bmc1_min_bound                        0
% 2.73/1.02  --bmc1_max_bound                        -1
% 2.73/1.02  --bmc1_max_bound_default                -1
% 2.73/1.02  --bmc1_symbol_reachability              true
% 2.73/1.02  --bmc1_property_lemmas                  false
% 2.73/1.02  --bmc1_k_induction                      false
% 2.73/1.02  --bmc1_non_equiv_states                 false
% 2.73/1.02  --bmc1_deadlock                         false
% 2.73/1.02  --bmc1_ucm                              false
% 2.73/1.02  --bmc1_add_unsat_core                   none
% 2.73/1.02  --bmc1_unsat_core_children              false
% 2.73/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.02  --bmc1_out_stat                         full
% 2.73/1.02  --bmc1_ground_init                      false
% 2.73/1.02  --bmc1_pre_inst_next_state              false
% 2.73/1.02  --bmc1_pre_inst_state                   false
% 2.73/1.02  --bmc1_pre_inst_reach_state             false
% 2.73/1.02  --bmc1_out_unsat_core                   false
% 2.73/1.02  --bmc1_aig_witness_out                  false
% 2.73/1.02  --bmc1_verbose                          false
% 2.73/1.02  --bmc1_dump_clauses_tptp                false
% 2.73/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.02  --bmc1_dump_file                        -
% 2.73/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.02  --bmc1_ucm_extend_mode                  1
% 2.73/1.02  --bmc1_ucm_init_mode                    2
% 2.73/1.02  --bmc1_ucm_cone_mode                    none
% 2.73/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.02  --bmc1_ucm_relax_model                  4
% 2.73/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.02  --bmc1_ucm_layered_model                none
% 2.73/1.02  --bmc1_ucm_max_lemma_size               10
% 2.73/1.02  
% 2.73/1.02  ------ AIG Options
% 2.73/1.02  
% 2.73/1.02  --aig_mode                              false
% 2.73/1.02  
% 2.73/1.02  ------ Instantiation Options
% 2.73/1.02  
% 2.73/1.02  --instantiation_flag                    true
% 2.73/1.02  --inst_sos_flag                         false
% 2.73/1.02  --inst_sos_phase                        true
% 2.73/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.02  --inst_lit_sel_side                     none
% 2.73/1.02  --inst_solver_per_active                1400
% 2.73/1.02  --inst_solver_calls_frac                1.
% 2.73/1.02  --inst_passive_queue_type               priority_queues
% 2.73/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.02  --inst_passive_queues_freq              [25;2]
% 2.73/1.02  --inst_dismatching                      true
% 2.73/1.02  --inst_eager_unprocessed_to_passive     true
% 2.73/1.02  --inst_prop_sim_given                   true
% 2.73/1.02  --inst_prop_sim_new                     false
% 2.73/1.02  --inst_subs_new                         false
% 2.73/1.02  --inst_eq_res_simp                      false
% 2.73/1.02  --inst_subs_given                       false
% 2.73/1.02  --inst_orphan_elimination               true
% 2.73/1.02  --inst_learning_loop_flag               true
% 2.73/1.02  --inst_learning_start                   3000
% 2.73/1.02  --inst_learning_factor                  2
% 2.73/1.02  --inst_start_prop_sim_after_learn       3
% 2.73/1.02  --inst_sel_renew                        solver
% 2.73/1.02  --inst_lit_activity_flag                true
% 2.73/1.02  --inst_restr_to_given                   false
% 2.73/1.02  --inst_activity_threshold               500
% 2.73/1.02  --inst_out_proof                        true
% 2.73/1.02  
% 2.73/1.02  ------ Resolution Options
% 2.73/1.02  
% 2.73/1.02  --resolution_flag                       false
% 2.73/1.02  --res_lit_sel                           adaptive
% 2.73/1.02  --res_lit_sel_side                      none
% 2.73/1.02  --res_ordering                          kbo
% 2.73/1.02  --res_to_prop_solver                    active
% 2.73/1.02  --res_prop_simpl_new                    false
% 2.73/1.02  --res_prop_simpl_given                  true
% 2.73/1.02  --res_passive_queue_type                priority_queues
% 2.73/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.02  --res_passive_queues_freq               [15;5]
% 2.73/1.02  --res_forward_subs                      full
% 2.73/1.02  --res_backward_subs                     full
% 2.73/1.02  --res_forward_subs_resolution           true
% 2.73/1.02  --res_backward_subs_resolution          true
% 2.73/1.02  --res_orphan_elimination                true
% 2.73/1.02  --res_time_limit                        2.
% 2.73/1.02  --res_out_proof                         true
% 2.73/1.02  
% 2.73/1.02  ------ Superposition Options
% 2.73/1.02  
% 2.73/1.02  --superposition_flag                    true
% 2.73/1.02  --sup_passive_queue_type                priority_queues
% 2.73/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.02  --demod_completeness_check              fast
% 2.73/1.02  --demod_use_ground                      true
% 2.73/1.02  --sup_to_prop_solver                    passive
% 2.73/1.02  --sup_prop_simpl_new                    true
% 2.73/1.02  --sup_prop_simpl_given                  true
% 2.73/1.02  --sup_fun_splitting                     false
% 2.73/1.02  --sup_smt_interval                      50000
% 2.73/1.02  
% 2.73/1.02  ------ Superposition Simplification Setup
% 2.73/1.02  
% 2.73/1.02  --sup_indices_passive                   []
% 2.73/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.02  --sup_full_bw                           [BwDemod]
% 2.73/1.02  --sup_immed_triv                        [TrivRules]
% 2.73/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.02  --sup_immed_bw_main                     []
% 2.73/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.02  
% 2.73/1.02  ------ Combination Options
% 2.73/1.02  
% 2.73/1.02  --comb_res_mult                         3
% 2.73/1.02  --comb_sup_mult                         2
% 2.73/1.02  --comb_inst_mult                        10
% 2.73/1.02  
% 2.73/1.02  ------ Debug Options
% 2.73/1.02  
% 2.73/1.02  --dbg_backtrace                         false
% 2.73/1.02  --dbg_dump_prop_clauses                 false
% 2.73/1.02  --dbg_dump_prop_clauses_file            -
% 2.73/1.02  --dbg_out_stat                          false
% 2.73/1.02  
% 2.73/1.02  
% 2.73/1.02  
% 2.73/1.02  
% 2.73/1.02  ------ Proving...
% 2.73/1.02  
% 2.73/1.02  
% 2.73/1.02  % SZS status Theorem for theBenchmark.p
% 2.73/1.02  
% 2.73/1.02   Resolution empty clause
% 2.73/1.02  
% 2.73/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/1.02  
% 2.73/1.02  fof(f17,axiom,(
% 2.73/1.02    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.02  
% 2.73/1.02  fof(f27,plain,(
% 2.73/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.73/1.02    inference(ennf_transformation,[],[f17])).
% 2.73/1.02  
% 2.73/1.02  fof(f28,plain,(
% 2.73/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.73/1.02    inference(flattening,[],[f27])).
% 2.73/1.02  
% 2.73/1.02  fof(f72,plain,(
% 2.73/1.02    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.73/1.02    inference(cnf_transformation,[],[f28])).
% 2.73/1.02  
% 2.73/1.02  fof(f18,axiom,(
% 2.73/1.02    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 2.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.02  
% 2.73/1.02  fof(f29,plain,(
% 2.73/1.02    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 2.73/1.02    inference(ennf_transformation,[],[f18])).
% 2.73/1.02  
% 2.73/1.02  fof(f42,plain,(
% 2.73/1.02    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.73/1.02    inference(nnf_transformation,[],[f29])).
% 2.73/1.02  
% 2.73/1.02  fof(f43,plain,(
% 2.73/1.02    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.73/1.02    inference(rectify,[],[f42])).
% 2.73/1.02  
% 2.73/1.02  fof(f44,plain,(
% 2.73/1.02    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 2.73/1.02    introduced(choice_axiom,[])).
% 2.73/1.02  
% 2.73/1.02  fof(f45,plain,(
% 2.73/1.02    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.73/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 2.73/1.02  
% 2.73/1.02  fof(f73,plain,(
% 2.73/1.02    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.73/1.02    inference(cnf_transformation,[],[f45])).
% 2.73/1.02  
% 2.73/1.02  fof(f19,conjecture,(
% 2.73/1.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.02  
% 2.73/1.02  fof(f20,negated_conjecture,(
% 2.73/1.02    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.73/1.02    inference(negated_conjecture,[],[f19])).
% 2.73/1.02  
% 2.73/1.02  fof(f30,plain,(
% 2.73/1.02    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 2.73/1.02    inference(ennf_transformation,[],[f20])).
% 2.73/1.02  
% 2.73/1.02  fof(f31,plain,(
% 2.73/1.02    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.73/1.02    inference(flattening,[],[f30])).
% 2.73/1.02  
% 2.73/1.02  fof(f47,plain,(
% 2.73/1.02    ( ! [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK4 != X0 & r1_tarski(X0,sK4) & v1_zfmisc_1(sK4) & ~v1_xboole_0(sK4))) )),
% 2.73/1.02    introduced(choice_axiom,[])).
% 2.73/1.02  
% 2.73/1.02  fof(f46,plain,(
% 2.73/1.02    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK3 != X1 & r1_tarski(sK3,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK3))),
% 2.73/1.02    introduced(choice_axiom,[])).
% 2.73/1.02  
% 2.73/1.02  fof(f48,plain,(
% 2.73/1.02    (sK3 != sK4 & r1_tarski(sK3,sK4) & v1_zfmisc_1(sK4) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 2.73/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f47,f46])).
% 2.73/1.02  
% 2.73/1.02  fof(f78,plain,(
% 2.73/1.02    v1_zfmisc_1(sK4)),
% 2.73/1.02    inference(cnf_transformation,[],[f48])).
% 2.73/1.02  
% 2.73/1.02  fof(f77,plain,(
% 2.73/1.02    ~v1_xboole_0(sK4)),
% 2.73/1.02    inference(cnf_transformation,[],[f48])).
% 2.73/1.02  
% 2.73/1.02  fof(f74,plain,(
% 2.73/1.02    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.73/1.02    inference(cnf_transformation,[],[f45])).
% 2.73/1.02  
% 2.73/1.02  fof(f79,plain,(
% 2.73/1.02    r1_tarski(sK3,sK4)),
% 2.73/1.02    inference(cnf_transformation,[],[f48])).
% 2.73/1.02  
% 2.73/1.02  fof(f6,axiom,(
% 2.73/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.02  
% 2.73/1.02  fof(f22,plain,(
% 2.73/1.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.73/1.02    inference(ennf_transformation,[],[f6])).
% 2.73/1.02  
% 2.73/1.02  fof(f61,plain,(
% 2.73/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.73/1.02    inference(cnf_transformation,[],[f22])).
% 2.73/1.02  
% 2.73/1.02  fof(f14,axiom,(
% 2.73/1.02    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.02  
% 2.73/1.02  fof(f25,plain,(
% 2.73/1.02    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 2.73/1.02    inference(ennf_transformation,[],[f14])).
% 2.73/1.02  
% 2.73/1.02  fof(f69,plain,(
% 2.73/1.02    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 2.73/1.02    inference(cnf_transformation,[],[f25])).
% 2.73/1.02  
% 2.73/1.02  fof(f9,axiom,(
% 2.73/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.02  
% 2.73/1.02  fof(f64,plain,(
% 2.73/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.73/1.02    inference(cnf_transformation,[],[f9])).
% 2.73/1.02  
% 2.73/1.02  fof(f2,axiom,(
% 2.73/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.02  
% 2.73/1.02  fof(f32,plain,(
% 2.73/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.73/1.02    inference(nnf_transformation,[],[f2])).
% 2.73/1.02  
% 2.73/1.02  fof(f33,plain,(
% 2.73/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.73/1.02    inference(rectify,[],[f32])).
% 2.73/1.02  
% 2.73/1.02  fof(f34,plain,(
% 2.73/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.73/1.02    introduced(choice_axiom,[])).
% 2.73/1.02  
% 2.73/1.02  fof(f35,plain,(
% 2.73/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.73/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 2.73/1.02  
% 2.73/1.02  fof(f51,plain,(
% 2.73/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.73/1.02    inference(cnf_transformation,[],[f35])).
% 2.73/1.02  
% 2.73/1.02  fof(f76,plain,(
% 2.73/1.02    ~v1_xboole_0(sK3)),
% 2.73/1.02    inference(cnf_transformation,[],[f48])).
% 2.73/1.02  
% 2.73/1.02  fof(f16,axiom,(
% 2.73/1.02    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.02  
% 2.73/1.02  fof(f26,plain,(
% 2.73/1.02    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.73/1.02    inference(ennf_transformation,[],[f16])).
% 2.73/1.02  
% 2.73/1.02  fof(f71,plain,(
% 2.73/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.73/1.02    inference(cnf_transformation,[],[f26])).
% 2.73/1.02  
% 2.73/1.02  fof(f8,axiom,(
% 2.73/1.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.73/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.02  
% 2.73/1.02  fof(f23,plain,(
% 2.73/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.73/1.02    inference(ennf_transformation,[],[f8])).
% 2.73/1.02  
% 2.73/1.02  fof(f24,plain,(
% 2.73/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.73/1.02    inference(flattening,[],[f23])).
% 2.73/1.02  
% 2.73/1.02  fof(f63,plain,(
% 2.73/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.73/1.02    inference(cnf_transformation,[],[f24])).
% 2.73/1.02  
% 2.73/1.02  fof(f80,plain,(
% 2.73/1.02    sK3 != sK4),
% 2.73/1.02    inference(cnf_transformation,[],[f48])).
% 2.73/1.02  
% 2.73/1.02  cnf(c_22,plain,
% 2.73/1.02      ( ~ m1_subset_1(X0,X1)
% 2.73/1.02      | v1_xboole_0(X1)
% 2.73/1.02      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.73/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_25,plain,
% 2.73/1.02      ( m1_subset_1(sK2(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 2.73/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_333,plain,
% 2.73/1.02      ( ~ v1_zfmisc_1(X0)
% 2.73/1.02      | v1_xboole_0(X1)
% 2.73/1.02      | v1_xboole_0(X0)
% 2.73/1.02      | X0 != X1
% 2.73/1.02      | k6_domain_1(X1,X2) = k1_tarski(X2)
% 2.73/1.02      | sK2(X0) != X2 ),
% 2.73/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_25]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_334,plain,
% 2.73/1.02      ( ~ v1_zfmisc_1(X0)
% 2.73/1.02      | v1_xboole_0(X0)
% 2.73/1.02      | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0)) ),
% 2.73/1.02      inference(unflattening,[status(thm)],[c_333]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_28,negated_conjecture,
% 2.73/1.02      ( v1_zfmisc_1(sK4) ),
% 2.73/1.02      inference(cnf_transformation,[],[f78]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_352,plain,
% 2.73/1.02      ( v1_xboole_0(X0)
% 2.73/1.02      | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0))
% 2.73/1.02      | sK4 != X0 ),
% 2.73/1.02      inference(resolution_lifted,[status(thm)],[c_334,c_28]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_353,plain,
% 2.73/1.02      ( v1_xboole_0(sK4) | k6_domain_1(sK4,sK2(sK4)) = k1_tarski(sK2(sK4)) ),
% 2.73/1.02      inference(unflattening,[status(thm)],[c_352]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_29,negated_conjecture,
% 2.73/1.02      ( ~ v1_xboole_0(sK4) ),
% 2.73/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_355,plain,
% 2.73/1.02      ( k6_domain_1(sK4,sK2(sK4)) = k1_tarski(sK2(sK4)) ),
% 2.73/1.02      inference(global_propositional_subsumption,[status(thm)],[c_353,c_29]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_24,plain,
% 2.73/1.02      ( ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = X0 ),
% 2.73/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_360,plain,
% 2.73/1.02      ( v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = X0 | sK4 != X0 ),
% 2.73/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_361,plain,
% 2.73/1.02      ( v1_xboole_0(sK4) | k6_domain_1(sK4,sK2(sK4)) = sK4 ),
% 2.73/1.02      inference(unflattening,[status(thm)],[c_360]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_363,plain,
% 2.73/1.02      ( k6_domain_1(sK4,sK2(sK4)) = sK4 ),
% 2.73/1.02      inference(global_propositional_subsumption,[status(thm)],[c_361,c_29]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1058,plain,
% 2.73/1.02      ( k1_tarski(sK2(sK4)) = sK4 ),
% 2.73/1.02      inference(light_normalisation,[status(thm)],[c_355,c_363]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_27,negated_conjecture,
% 2.73/1.02      ( r1_tarski(sK3,sK4) ),
% 2.73/1.02      inference(cnf_transformation,[],[f79]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1021,plain,
% 2.73/1.02      ( r1_tarski(sK3,sK4) = iProver_top ),
% 2.73/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_12,plain,
% 2.73/1.02      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 2.73/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1026,plain,
% 2.73/1.02      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 2.73/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_3305,plain,
% 2.73/1.02      ( k2_xboole_0(sK3,sK4) = sK4 ),
% 2.73/1.02      inference(superposition,[status(thm)],[c_1021,c_1026]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_19,plain,
% 2.73/1.02      ( X0 = X1
% 2.73/1.02      | k2_xboole_0(X1,X0) != k1_tarski(X2)
% 2.73/1.02      | k1_xboole_0 = X0
% 2.73/1.02      | k1_xboole_0 = X1 ),
% 2.73/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_3478,plain,
% 2.73/1.02      ( k1_tarski(X0) != sK4
% 2.73/1.02      | sK4 = sK3
% 2.73/1.02      | sK4 = k1_xboole_0
% 2.73/1.02      | sK3 = k1_xboole_0 ),
% 2.73/1.02      inference(superposition,[status(thm)],[c_3305,c_19]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_15,plain,
% 2.73/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 2.73/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_58,plain,
% 2.73/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1,plain,
% 2.73/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.73/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_382,plain,
% 2.73/1.02      ( r2_hidden(sK0(X0),X0) | sK4 != X0 ),
% 2.73/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_29]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_383,plain,
% 2.73/1.02      ( r2_hidden(sK0(sK4),sK4) ),
% 2.73/1.02      inference(unflattening,[status(thm)],[c_382]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_30,negated_conjecture,
% 2.73/1.02      ( ~ v1_xboole_0(sK3) ),
% 2.73/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_389,plain,
% 2.73/1.02      ( r2_hidden(sK0(X0),X0) | sK3 != X0 ),
% 2.73/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_30]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_390,plain,
% 2.73/1.02      ( r2_hidden(sK0(sK3),sK3) ),
% 2.73/1.02      inference(unflattening,[status(thm)],[c_389]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_578,plain,( X0 = X0 ),theory(equality) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_598,plain,
% 2.73/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_578]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_21,plain,
% 2.73/1.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.73/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1190,plain,
% 2.73/1.02      ( ~ r1_tarski(sK4,sK0(sK4)) | ~ r2_hidden(sK0(sK4),sK4) ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_21]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1193,plain,
% 2.73/1.02      ( ~ r1_tarski(sK3,sK0(sK3)) | ~ r2_hidden(sK0(sK3),sK3) ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_21]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_14,plain,
% 2.73/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.73/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1287,plain,
% 2.73/1.02      ( ~ r1_tarski(X0,sK0(sK4))
% 2.73/1.02      | ~ r1_tarski(sK4,X0)
% 2.73/1.02      | r1_tarski(sK4,sK0(sK4)) ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1289,plain,
% 2.73/1.02      ( r1_tarski(sK4,sK0(sK4))
% 2.73/1.02      | ~ r1_tarski(sK4,k1_xboole_0)
% 2.73/1.02      | ~ r1_tarski(k1_xboole_0,sK0(sK4)) ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_1287]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1300,plain,
% 2.73/1.02      ( ~ r1_tarski(X0,sK0(sK3))
% 2.73/1.02      | ~ r1_tarski(sK3,X0)
% 2.73/1.02      | r1_tarski(sK3,sK0(sK3)) ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1302,plain,
% 2.73/1.02      ( r1_tarski(sK3,sK0(sK3))
% 2.73/1.02      | ~ r1_tarski(sK3,k1_xboole_0)
% 2.73/1.02      | ~ r1_tarski(k1_xboole_0,sK0(sK3)) ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_1300]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_584,plain,
% 2.73/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.73/1.02      theory(equality) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1593,plain,
% 2.73/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,X2) | X2 != X1 | sK4 != X0 ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_584]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1595,plain,
% 2.73/1.02      ( r1_tarski(sK4,k1_xboole_0)
% 2.73/1.02      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.73/1.02      | sK4 != k1_xboole_0
% 2.73/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_1593]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1620,plain,
% 2.73/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_584]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_1622,plain,
% 2.73/1.02      ( r1_tarski(sK3,k1_xboole_0)
% 2.73/1.02      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.73/1.02      | sK3 != k1_xboole_0
% 2.73/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_1620]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_2171,plain,
% 2.73/1.02      ( r1_tarski(k1_xboole_0,sK0(sK4)) ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_4267,plain,
% 2.73/1.02      ( r1_tarski(k1_xboole_0,sK0(sK3)) ),
% 2.73/1.02      inference(instantiation,[status(thm)],[c_15]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_4343,plain,
% 2.73/1.02      ( k1_tarski(X0) != sK4 | sK4 = sK3 ),
% 2.73/1.02      inference(global_propositional_subsumption,
% 2.73/1.02                [status(thm)],
% 2.73/1.02                [c_3478,c_58,c_383,c_390,c_598,c_1190,c_1193,c_1289,c_1302,
% 2.73/1.02                 c_1595,c_1622,c_2171,c_4267]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_4348,plain,
% 2.73/1.02      ( sK4 = sK3 ),
% 2.73/1.02      inference(superposition,[status(thm)],[c_1058,c_4343]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_26,negated_conjecture,
% 2.73/1.02      ( sK3 != sK4 ),
% 2.73/1.02      inference(cnf_transformation,[],[f80]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_4857,plain,
% 2.73/1.02      ( sK3 != sK3 ),
% 2.73/1.02      inference(demodulation,[status(thm)],[c_4348,c_26]) ).
% 2.73/1.02  
% 2.73/1.02  cnf(c_4858,plain,
% 2.73/1.02      ( $false ),
% 2.73/1.02      inference(equality_resolution_simp,[status(thm)],[c_4857]) ).
% 2.73/1.02  
% 2.73/1.02  
% 2.73/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/1.02  
% 2.73/1.02  ------                               Statistics
% 2.73/1.02  
% 2.73/1.02  ------ General
% 2.73/1.02  
% 2.73/1.02  abstr_ref_over_cycles:                  0
% 2.73/1.02  abstr_ref_under_cycles:                 0
% 2.73/1.02  gc_basic_clause_elim:                   0
% 2.73/1.02  forced_gc_time:                         0
% 2.73/1.02  parsing_time:                           0.008
% 2.73/1.02  unif_index_cands_time:                  0.
% 2.73/1.02  unif_index_add_time:                    0.
% 2.73/1.02  orderings_time:                         0.
% 2.73/1.02  out_proof_time:                         0.007
% 2.73/1.02  total_time:                             0.15
% 2.73/1.02  num_of_symbols:                         48
% 2.73/1.02  num_of_terms:                           4556
% 2.73/1.02  
% 2.73/1.02  ------ Preprocessing
% 2.73/1.02  
% 2.73/1.02  num_of_splits:                          0
% 2.73/1.02  num_of_split_atoms:                     0
% 2.73/1.02  num_of_reused_defs:                     0
% 2.73/1.02  num_eq_ax_congr_red:                    26
% 2.73/1.02  num_of_sem_filtered_clauses:            1
% 2.73/1.02  num_of_subtypes:                        0
% 2.73/1.02  monotx_restored_types:                  0
% 2.73/1.02  sat_num_of_epr_types:                   0
% 2.73/1.02  sat_num_of_non_cyclic_types:            0
% 2.73/1.02  sat_guarded_non_collapsed_types:        0
% 2.73/1.02  num_pure_diseq_elim:                    0
% 2.73/1.02  simp_replaced_by:                       0
% 2.73/1.02  res_preprocessed:                       135
% 2.73/1.02  prep_upred:                             0
% 2.73/1.02  prep_unflattend:                        9
% 2.73/1.02  smt_new_axioms:                         0
% 2.73/1.02  pred_elim_cands:                        2
% 2.73/1.02  pred_elim:                              3
% 2.73/1.02  pred_elim_cl:                           4
% 2.73/1.02  pred_elim_cycles:                       5
% 2.73/1.02  merged_defs:                            8
% 2.73/1.02  merged_defs_ncl:                        0
% 2.73/1.02  bin_hyper_res:                          8
% 2.73/1.02  prep_cycles:                            4
% 2.73/1.02  pred_elim_time:                         0.002
% 2.73/1.02  splitting_time:                         0.
% 2.73/1.02  sem_filter_time:                        0.
% 2.73/1.02  monotx_time:                            0.
% 2.73/1.02  subtype_inf_time:                       0.
% 2.73/1.02  
% 2.73/1.02  ------ Problem properties
% 2.73/1.02  
% 2.73/1.02  clauses:                                27
% 2.73/1.02  conjectures:                            2
% 2.73/1.02  epr:                                    5
% 2.73/1.02  horn:                                   24
% 2.73/1.02  ground:                                 6
% 2.73/1.02  unary:                                  13
% 2.73/1.02  binary:                                 8
% 2.73/1.02  lits:                                   49
% 2.73/1.02  lits_eq:                                18
% 2.73/1.02  fd_pure:                                0
% 2.73/1.02  fd_pseudo:                              0
% 2.73/1.02  fd_cond:                                0
% 2.73/1.02  fd_pseudo_cond:                         4
% 2.73/1.02  ac_symbols:                             0
% 2.73/1.02  
% 2.73/1.02  ------ Propositional Solver
% 2.73/1.02  
% 2.73/1.02  prop_solver_calls:                      27
% 2.73/1.02  prop_fast_solver_calls:                 605
% 2.73/1.02  smt_solver_calls:                       0
% 2.73/1.02  smt_fast_solver_calls:                  0
% 2.73/1.02  prop_num_of_clauses:                    1950
% 2.73/1.02  prop_preprocess_simplified:             6932
% 2.73/1.02  prop_fo_subsumed:                       4
% 2.73/1.02  prop_solver_time:                       0.
% 2.73/1.02  smt_solver_time:                        0.
% 2.73/1.02  smt_fast_solver_time:                   0.
% 2.73/1.02  prop_fast_solver_time:                  0.
% 2.73/1.02  prop_unsat_core_time:                   0.
% 2.73/1.02  
% 2.73/1.02  ------ QBF
% 2.73/1.02  
% 2.73/1.02  qbf_q_res:                              0
% 2.73/1.02  qbf_num_tautologies:                    0
% 2.73/1.02  qbf_prep_cycles:                        0
% 2.73/1.02  
% 2.73/1.02  ------ BMC1
% 2.73/1.02  
% 2.73/1.02  bmc1_current_bound:                     -1
% 2.73/1.02  bmc1_last_solved_bound:                 -1
% 2.73/1.02  bmc1_unsat_core_size:                   -1
% 2.73/1.02  bmc1_unsat_core_parents_size:           -1
% 2.73/1.02  bmc1_merge_next_fun:                    0
% 2.73/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.73/1.02  
% 2.73/1.02  ------ Instantiation
% 2.73/1.02  
% 2.73/1.02  inst_num_of_clauses:                    668
% 2.73/1.02  inst_num_in_passive:                    451
% 2.73/1.02  inst_num_in_active:                     219
% 2.73/1.02  inst_num_in_unprocessed:                0
% 2.73/1.02  inst_num_of_loops:                      230
% 2.73/1.02  inst_num_of_learning_restarts:          0
% 2.73/1.02  inst_num_moves_active_passive:          10
% 2.73/1.02  inst_lit_activity:                      0
% 2.73/1.02  inst_lit_activity_moves:                0
% 2.73/1.02  inst_num_tautologies:                   0
% 2.73/1.02  inst_num_prop_implied:                  0
% 2.73/1.02  inst_num_existing_simplified:           0
% 2.73/1.02  inst_num_eq_res_simplified:             0
% 2.73/1.02  inst_num_child_elim:                    0
% 2.73/1.02  inst_num_of_dismatching_blockings:      65
% 2.73/1.02  inst_num_of_non_proper_insts:           408
% 2.73/1.02  inst_num_of_duplicates:                 0
% 2.73/1.02  inst_inst_num_from_inst_to_res:         0
% 2.73/1.02  inst_dismatching_checking_time:         0.
% 2.73/1.02  
% 2.73/1.02  ------ Resolution
% 2.73/1.02  
% 2.73/1.02  res_num_of_clauses:                     0
% 2.73/1.02  res_num_in_passive:                     0
% 2.73/1.02  res_num_in_active:                      0
% 2.73/1.02  res_num_of_loops:                       139
% 2.73/1.02  res_forward_subset_subsumed:            49
% 2.73/1.02  res_backward_subset_subsumed:           4
% 2.73/1.02  res_forward_subsumed:                   0
% 2.73/1.02  res_backward_subsumed:                  0
% 2.73/1.02  res_forward_subsumption_resolution:     0
% 2.73/1.02  res_backward_subsumption_resolution:    0
% 2.73/1.02  res_clause_to_clause_subsumption:       187
% 2.73/1.02  res_orphan_elimination:                 0
% 2.73/1.02  res_tautology_del:                      34
% 2.73/1.02  res_num_eq_res_simplified:              0
% 2.73/1.02  res_num_sel_changes:                    0
% 2.73/1.02  res_moves_from_active_to_pass:          0
% 2.73/1.02  
% 2.73/1.02  ------ Superposition
% 2.73/1.02  
% 2.73/1.02  sup_time_total:                         0.
% 2.73/1.02  sup_time_generating:                    0.
% 2.73/1.02  sup_time_sim_full:                      0.
% 2.73/1.02  sup_time_sim_immed:                     0.
% 2.73/1.02  
% 2.73/1.02  sup_num_of_clauses:                     56
% 2.73/1.02  sup_num_in_active:                      31
% 2.73/1.02  sup_num_in_passive:                     25
% 2.73/1.02  sup_num_of_loops:                       44
% 2.73/1.02  sup_fw_superposition:                   82
% 2.73/1.02  sup_bw_superposition:                   37
% 2.73/1.02  sup_immediate_simplified:               18
% 2.73/1.02  sup_given_eliminated:                   0
% 2.73/1.02  comparisons_done:                       0
% 2.73/1.02  comparisons_avoided:                    0
% 2.73/1.02  
% 2.73/1.02  ------ Simplifications
% 2.73/1.02  
% 2.73/1.02  
% 2.73/1.02  sim_fw_subset_subsumed:                 0
% 2.73/1.02  sim_bw_subset_subsumed:                 0
% 2.73/1.02  sim_fw_subsumed:                        8
% 2.73/1.02  sim_bw_subsumed:                        0
% 2.73/1.02  sim_fw_subsumption_res:                 0
% 2.73/1.02  sim_bw_subsumption_res:                 0
% 2.73/1.02  sim_tautology_del:                      1
% 2.73/1.02  sim_eq_tautology_del:                   8
% 2.73/1.02  sim_eq_res_simp:                        0
% 2.73/1.02  sim_fw_demodulated:                     9
% 2.73/1.02  sim_bw_demodulated:                     13
% 2.73/1.02  sim_light_normalised:                   13
% 2.73/1.02  sim_joinable_taut:                      0
% 2.73/1.02  sim_joinable_simp:                      0
% 2.73/1.02  sim_ac_normalised:                      0
% 2.73/1.02  sim_smt_subsumption:                    0
% 2.73/1.02  
%------------------------------------------------------------------------------
