%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:09 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 178 expanded)
%              Number of clauses        :   51 (  62 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  257 ( 529 expanded)
%              Number of equality atoms :   70 ( 101 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f87])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK7))
        & r1_tarski(X0,sK7)
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(X1))
          & r1_tarski(sK6,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
    & r1_tarski(sK6,sK7)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f63,f62])).

fof(f103,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f98,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f118,plain,(
    ! [X0] :
      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f98,f87])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f87])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f123,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f105,plain,(
    ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f64])).

fof(f104,plain,(
    r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f102,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2437,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK7))
    | ~ r1_tarski(X1,k3_relat_1(sK7))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k3_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_19382,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7))
    | ~ r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7))
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))),k3_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_2437])).

cnf(c_790,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1865,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
    | k3_relat_1(sK7) != X1
    | k3_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_6496,plain,
    ( r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))),X0)
    | k3_relat_1(sK7) != X0
    | k3_relat_1(sK6) != k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_1865])).

cnf(c_9102,plain,
    ( r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))),k3_relat_1(sK7))
    | k3_relat_1(sK7) != k3_relat_1(sK7)
    | k3_relat_1(sK6) != k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))) ),
    inference(instantiation,[status(thm)],[c_6496])).

cnf(c_34,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_207,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34,c_26,c_24])).

cnf(c_208,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_207])).

cnf(c_1551,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1553,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_31,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1557,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3000,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1553,c_1557])).

cnf(c_21,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1570,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3321,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1570])).

cnf(c_4914,plain,
    ( r1_tarski(X0,k3_relat_1(sK7)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3000,c_3321])).

cnf(c_6006,plain,
    ( r1_tarski(X0,sK7) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1551,c_4914])).

cnf(c_6021,plain,
    ( ~ r1_tarski(X0,sK7)
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6006])).

cnf(c_6023,plain,
    ( r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7))
    | ~ r1_tarski(sK6,sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_6021])).

cnf(c_33,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_212,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_26,c_24])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_1550,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_3320,plain,
    ( r1_tarski(X0,k3_relat_1(sK7)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3000,c_1570])).

cnf(c_3908,plain,
    ( r1_tarski(X0,sK7) != iProver_top
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_3320])).

cnf(c_3924,plain,
    ( ~ r1_tarski(X0,sK7)
    | r1_tarski(k2_relat_1(X0),k3_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3908])).

cnf(c_3926,plain,
    ( r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7))
    | ~ r1_tarski(sK6,sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3924])).

cnf(c_788,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2025,plain,
    ( X0 != X1
    | k3_relat_1(sK6) != X1
    | k3_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_2453,plain,
    ( X0 != k3_relat_1(sK6)
    | k3_relat_1(sK6) = X0
    | k3_relat_1(sK6) != k3_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2025])).

cnf(c_3472,plain,
    ( k3_relat_1(sK6) != k3_relat_1(sK6)
    | k3_relat_1(sK6) = k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6)))
    | k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))) != k3_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2453])).

cnf(c_787,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2458,plain,
    ( k3_relat_1(sK7) = k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_797,plain,
    ( X0 != X1
    | k3_relat_1(X0) = k3_relat_1(X1) ),
    theory(equality)).

cnf(c_805,plain,
    ( k3_relat_1(sK6) = k3_relat_1(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_106,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_102,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_53,plain,
    ( ~ v1_relat_1(sK6)
    | k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))) = k3_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_35,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(sK6,sK7) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_38,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f102])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19382,c_9102,c_6023,c_3926,c_3472,c_2458,c_805,c_106,c_102,c_53,c_35,c_36,c_37,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:19:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.53/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/0.99  
% 3.53/0.99  ------  iProver source info
% 3.53/0.99  
% 3.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/0.99  git: non_committed_changes: false
% 3.53/0.99  git: last_make_outside_of_git: false
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  ------ Parsing...
% 3.53/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.99  ------ Proving...
% 3.53/0.99  ------ Problem Properties 
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  clauses                                 36
% 3.53/0.99  conjectures                             4
% 3.53/0.99  EPR                                     10
% 3.53/0.99  Horn                                    32
% 3.53/0.99  unary                                   9
% 3.53/0.99  binary                                  12
% 3.53/0.99  lits                                    79
% 3.53/0.99  lits eq                                 9
% 3.53/0.99  fd_pure                                 0
% 3.53/0.99  fd_pseudo                               0
% 3.53/0.99  fd_cond                                 0
% 3.53/0.99  fd_pseudo_cond                          6
% 3.53/0.99  AC symbols                              0
% 3.53/0.99  
% 3.53/0.99  ------ Input Options Time Limit: Unbounded
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  Current options:
% 3.53/0.99  ------ 
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ Proving...
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  % SZS status Theorem for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  fof(f12,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f32,plain,(
% 3.53/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.53/0.99    inference(ennf_transformation,[],[f12])).
% 3.53/0.99  
% 3.53/0.99  fof(f33,plain,(
% 3.53/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.53/0.99    inference(flattening,[],[f32])).
% 3.53/0.99  
% 3.53/0.99  fof(f85,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f33])).
% 3.53/0.99  
% 3.53/0.99  fof(f14,axiom,(
% 3.53/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f87,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f14])).
% 3.53/0.99  
% 3.53/0.99  fof(f117,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f85,f87])).
% 3.53/0.99  
% 3.53/0.99  fof(f22,axiom,(
% 3.53/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f38,plain,(
% 3.53/0.99    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.53/0.99    inference(ennf_transformation,[],[f22])).
% 3.53/0.99  
% 3.53/0.99  fof(f39,plain,(
% 3.53/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.53/0.99    inference(flattening,[],[f38])).
% 3.53/0.99  
% 3.53/0.99  fof(f100,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f39])).
% 3.53/0.99  
% 3.53/0.99  fof(f18,axiom,(
% 3.53/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f35,plain,(
% 3.53/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.53/0.99    inference(ennf_transformation,[],[f18])).
% 3.53/0.99  
% 3.53/0.99  fof(f93,plain,(
% 3.53/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f35])).
% 3.53/0.99  
% 3.53/0.99  fof(f17,axiom,(
% 3.53/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f55,plain,(
% 3.53/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.53/0.99    inference(nnf_transformation,[],[f17])).
% 3.53/0.99  
% 3.53/0.99  fof(f92,plain,(
% 3.53/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f55])).
% 3.53/0.99  
% 3.53/0.99  fof(f23,conjecture,(
% 3.53/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f24,negated_conjecture,(
% 3.53/0.99    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.53/0.99    inference(negated_conjecture,[],[f23])).
% 3.53/0.99  
% 3.53/0.99  fof(f40,plain,(
% 3.53/0.99    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.53/0.99    inference(ennf_transformation,[],[f24])).
% 3.53/0.99  
% 3.53/0.99  fof(f41,plain,(
% 3.53/0.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.53/0.99    inference(flattening,[],[f40])).
% 3.53/0.99  
% 3.53/0.99  fof(f63,plain,(
% 3.53/0.99    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK7)) & r1_tarski(X0,sK7) & v1_relat_1(sK7))) )),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f62,plain,(
% 3.53/0.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK6),k3_relat_1(X1)) & r1_tarski(sK6,X1) & v1_relat_1(X1)) & v1_relat_1(sK6))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f64,plain,(
% 3.53/0.99    (~r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) & r1_tarski(sK6,sK7) & v1_relat_1(sK7)) & v1_relat_1(sK6)),
% 3.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f63,f62])).
% 3.53/0.99  
% 3.53/0.99  fof(f103,plain,(
% 3.53/0.99    v1_relat_1(sK7)),
% 3.53/0.99    inference(cnf_transformation,[],[f64])).
% 3.53/0.99  
% 3.53/0.99  fof(f20,axiom,(
% 3.53/0.99    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f36,plain,(
% 3.53/0.99    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 3.53/0.99    inference(ennf_transformation,[],[f20])).
% 3.53/0.99  
% 3.53/0.99  fof(f98,plain,(
% 3.53/0.99    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f36])).
% 3.53/0.99  
% 3.53/0.99  fof(f118,plain,(
% 3.53/0.99    ( ! [X0] : (k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f98,f87])).
% 3.53/0.99  
% 3.53/0.99  fof(f13,axiom,(
% 3.53/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f86,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f13])).
% 3.53/0.99  
% 3.53/0.99  fof(f5,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f27,plain,(
% 3.53/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.53/0.99    inference(ennf_transformation,[],[f5])).
% 3.53/0.99  
% 3.53/0.99  fof(f78,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f27])).
% 3.53/0.99  
% 3.53/0.99  fof(f112,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f78,f87])).
% 3.53/0.99  
% 3.53/0.99  fof(f101,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f39])).
% 3.53/0.99  
% 3.53/0.99  fof(f4,axiom,(
% 3.53/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f51,plain,(
% 3.53/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/0.99    inference(nnf_transformation,[],[f4])).
% 3.53/0.99  
% 3.53/0.99  fof(f52,plain,(
% 3.53/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.53/0.99    inference(flattening,[],[f51])).
% 3.53/0.99  
% 3.53/0.99  fof(f77,plain,(
% 3.53/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f52])).
% 3.53/0.99  
% 3.53/0.99  fof(f75,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.53/0.99    inference(cnf_transformation,[],[f52])).
% 3.53/0.99  
% 3.53/0.99  fof(f123,plain,(
% 3.53/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.53/0.99    inference(equality_resolution,[],[f75])).
% 3.53/0.99  
% 3.53/0.99  fof(f105,plain,(
% 3.53/0.99    ~r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))),
% 3.53/0.99    inference(cnf_transformation,[],[f64])).
% 3.53/0.99  
% 3.53/0.99  fof(f104,plain,(
% 3.53/0.99    r1_tarski(sK6,sK7)),
% 3.53/0.99    inference(cnf_transformation,[],[f64])).
% 3.53/0.99  
% 3.53/0.99  fof(f102,plain,(
% 3.53/0.99    v1_relat_1(sK6)),
% 3.53/0.99    inference(cnf_transformation,[],[f64])).
% 3.53/0.99  
% 3.53/0.99  cnf(c_20,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1)
% 3.53/0.99      | ~ r1_tarski(X2,X1)
% 3.53/0.99      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2437,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,k3_relat_1(sK7))
% 3.53/0.99      | ~ r1_tarski(X1,k3_relat_1(sK7))
% 3.53/0.99      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k3_relat_1(sK7)) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_19382,plain,
% 3.53/0.99      ( ~ r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7))
% 3.53/0.99      | ~ r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7))
% 3.53/0.99      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))),k3_relat_1(sK7)) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_2437]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_790,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.53/0.99      theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1865,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1)
% 3.53/0.99      | r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
% 3.53/0.99      | k3_relat_1(sK7) != X1
% 3.53/0.99      | k3_relat_1(sK6) != X0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_790]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_6496,plain,
% 3.53/0.99      ( r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
% 3.53/0.99      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))),X0)
% 3.53/0.99      | k3_relat_1(sK7) != X0
% 3.53/0.99      | k3_relat_1(sK6) != k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_1865]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_9102,plain,
% 3.53/0.99      ( r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7))
% 3.53/0.99      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))),k3_relat_1(sK7))
% 3.53/0.99      | k3_relat_1(sK7) != k3_relat_1(sK7)
% 3.53/0.99      | k3_relat_1(sK6) != k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_6496]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_34,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1)
% 3.53/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.53/0.99      | ~ v1_relat_1(X0)
% 3.53/0.99      | ~ v1_relat_1(X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_26,plain,
% 3.53/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.53/0.99      | ~ v1_relat_1(X1)
% 3.53/0.99      | v1_relat_1(X0) ),
% 3.53/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_24,plain,
% 3.53/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_207,plain,
% 3.53/0.99      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.53/0.99      | ~ r1_tarski(X0,X1)
% 3.53/0.99      | ~ v1_relat_1(X1) ),
% 3.53/0.99      inference(global_propositional_subsumption,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_34,c_26,c_24]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_208,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1)
% 3.53/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.53/0.99      | ~ v1_relat_1(X1) ),
% 3.53/0.99      inference(renaming,[status(thm)],[c_207]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1551,plain,
% 3.53/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.53/0.99      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 3.53/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_208]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_37,negated_conjecture,
% 3.53/0.99      ( v1_relat_1(sK7) ),
% 3.53/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1553,plain,
% 3.53/0.99      ( v1_relat_1(sK7) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_31,plain,
% 3.53/0.99      ( ~ v1_relat_1(X0)
% 3.53/0.99      | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 3.53/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1557,plain,
% 3.53/0.99      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 3.53/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3000,plain,
% 3.53/0.99      ( k3_tarski(k2_tarski(k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1553,c_1557]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_21,plain,
% 3.53/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.53/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_13,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 3.53/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1570,plain,
% 3.53/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.53/0.99      | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3321,plain,
% 3.53/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.53/0.99      | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_21,c_1570]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4914,plain,
% 3.53/0.99      ( r1_tarski(X0,k3_relat_1(sK7)) = iProver_top
% 3.53/0.99      | r1_tarski(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_3000,c_3321]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_6006,plain,
% 3.53/0.99      ( r1_tarski(X0,sK7) != iProver_top
% 3.53/0.99      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK7)) = iProver_top
% 3.53/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1551,c_4914]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_6021,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,sK7)
% 3.53/0.99      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK7))
% 3.53/0.99      | ~ v1_relat_1(sK7) ),
% 3.53/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6006]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_6023,plain,
% 3.53/0.99      ( r1_tarski(k1_relat_1(sK6),k3_relat_1(sK7))
% 3.53/0.99      | ~ r1_tarski(sK6,sK7)
% 3.53/0.99      | ~ v1_relat_1(sK7) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_6021]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_33,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1)
% 3.53/0.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.53/0.99      | ~ v1_relat_1(X0)
% 3.53/0.99      | ~ v1_relat_1(X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_212,plain,
% 3.53/0.99      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.53/0.99      | ~ r1_tarski(X0,X1)
% 3.53/0.99      | ~ v1_relat_1(X1) ),
% 3.53/0.99      inference(global_propositional_subsumption,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_33,c_26,c_24]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_213,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1)
% 3.53/0.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.53/0.99      | ~ v1_relat_1(X1) ),
% 3.53/0.99      inference(renaming,[status(thm)],[c_212]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1550,plain,
% 3.53/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.53/0.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 3.53/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3320,plain,
% 3.53/0.99      ( r1_tarski(X0,k3_relat_1(sK7)) = iProver_top
% 3.53/0.99      | r1_tarski(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_3000,c_1570]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3908,plain,
% 3.53/0.99      ( r1_tarski(X0,sK7) != iProver_top
% 3.53/0.99      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK7)) = iProver_top
% 3.53/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1550,c_3320]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3924,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,sK7)
% 3.53/0.99      | r1_tarski(k2_relat_1(X0),k3_relat_1(sK7))
% 3.53/0.99      | ~ v1_relat_1(sK7) ),
% 3.53/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3908]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3926,plain,
% 3.53/0.99      ( r1_tarski(k2_relat_1(sK6),k3_relat_1(sK7))
% 3.53/0.99      | ~ r1_tarski(sK6,sK7)
% 3.53/0.99      | ~ v1_relat_1(sK7) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_3924]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_788,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2025,plain,
% 3.53/0.99      ( X0 != X1 | k3_relat_1(sK6) != X1 | k3_relat_1(sK6) = X0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_788]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2453,plain,
% 3.53/0.99      ( X0 != k3_relat_1(sK6)
% 3.53/0.99      | k3_relat_1(sK6) = X0
% 3.53/0.99      | k3_relat_1(sK6) != k3_relat_1(sK6) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_2025]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3472,plain,
% 3.53/0.99      ( k3_relat_1(sK6) != k3_relat_1(sK6)
% 3.53/0.99      | k3_relat_1(sK6) = k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6)))
% 3.53/0.99      | k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))) != k3_relat_1(sK6) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_2453]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_787,plain,( X0 = X0 ),theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2458,plain,
% 3.53/0.99      ( k3_relat_1(sK7) = k3_relat_1(sK7) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_787]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_797,plain,
% 3.53/0.99      ( X0 != X1 | k3_relat_1(X0) = k3_relat_1(X1) ),
% 3.53/0.99      theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_805,plain,
% 3.53/0.99      ( k3_relat_1(sK6) = k3_relat_1(sK6) | sK6 != sK6 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_797]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_10,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.53/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_106,plain,
% 3.53/0.99      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_12,plain,
% 3.53/0.99      ( r1_tarski(X0,X0) ),
% 3.53/0.99      inference(cnf_transformation,[],[f123]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_102,plain,
% 3.53/0.99      ( r1_tarski(sK6,sK6) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_53,plain,
% 3.53/0.99      ( ~ v1_relat_1(sK6)
% 3.53/0.99      | k3_tarski(k2_tarski(k1_relat_1(sK6),k2_relat_1(sK6))) = k3_relat_1(sK6) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_31]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_35,negated_conjecture,
% 3.53/0.99      ( ~ r1_tarski(k3_relat_1(sK6),k3_relat_1(sK7)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_36,negated_conjecture,
% 3.53/0.99      ( r1_tarski(sK6,sK7) ),
% 3.53/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_38,negated_conjecture,
% 3.53/0.99      ( v1_relat_1(sK6) ),
% 3.53/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(contradiction,plain,
% 3.53/0.99      ( $false ),
% 3.53/0.99      inference(minisat,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_19382,c_9102,c_6023,c_3926,c_3472,c_2458,c_805,c_106,
% 3.53/0.99                 c_102,c_53,c_35,c_36,c_37,c_38]) ).
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  ------                               Statistics
% 3.53/0.99  
% 3.53/0.99  ------ Selected
% 3.53/0.99  
% 3.53/0.99  total_time:                             0.492
% 3.53/0.99  
%------------------------------------------------------------------------------
