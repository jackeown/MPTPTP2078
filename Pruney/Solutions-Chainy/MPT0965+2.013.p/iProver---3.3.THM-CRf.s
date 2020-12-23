%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:22 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 148 expanded)
%              Number of clauses        :   38 (  46 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :   16
%              Number of atoms          :  247 ( 685 expanded)
%              Number of equality atoms :   94 ( 167 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK6,sK5),sK4)
      & k1_xboole_0 != sK4
      & r2_hidden(sK5,sK3)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK5),sK4)
    & k1_xboole_0 != sK4
    & r2_hidden(sK5,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f32,f48])).

fof(f79,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f65])).

fof(f77,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f37])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ~ r2_hidden(k1_funct_1(sK6,sK5),sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1203,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1209,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2919,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1203,c_1209])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X1
    | sK4 != X2
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_513,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_515,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_30,c_28])).

cnf(c_2920,plain,
    ( k1_relat_1(sK6) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2919,c_515])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_371,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_372,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1201,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_35,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_373,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1433,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1434,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1433])).

cnf(c_1871,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1201,c_35,c_373,c_1434])).

cnf(c_1872,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_1871])).

cnf(c_3502,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2920,c_1872])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4999,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_1214])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1218,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5087,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4999,c_1218])).

cnf(c_5851,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3502,c_5087])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK6,sK5),sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1205,plain,
    ( r2_hidden(k1_funct_1(sK6,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6300,plain,
    ( r2_hidden(sK5,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5851,c_1205])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_36,plain,
    ( r2_hidden(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6300,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:48:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.58/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.03  
% 2.58/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.58/1.03  
% 2.58/1.03  ------  iProver source info
% 2.58/1.03  
% 2.58/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.58/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.58/1.03  git: non_committed_changes: false
% 2.58/1.03  git: last_make_outside_of_git: false
% 2.58/1.03  
% 2.58/1.03  ------ 
% 2.58/1.03  
% 2.58/1.03  ------ Input Options
% 2.58/1.03  
% 2.58/1.03  --out_options                           all
% 2.58/1.03  --tptp_safe_out                         true
% 2.58/1.03  --problem_path                          ""
% 2.58/1.03  --include_path                          ""
% 2.58/1.03  --clausifier                            res/vclausify_rel
% 2.58/1.03  --clausifier_options                    --mode clausify
% 2.58/1.03  --stdin                                 false
% 2.58/1.03  --stats_out                             all
% 2.58/1.03  
% 2.58/1.03  ------ General Options
% 2.58/1.03  
% 2.58/1.03  --fof                                   false
% 2.58/1.03  --time_out_real                         305.
% 2.58/1.03  --time_out_virtual                      -1.
% 2.58/1.03  --symbol_type_check                     false
% 2.58/1.03  --clausify_out                          false
% 2.58/1.03  --sig_cnt_out                           false
% 2.58/1.03  --trig_cnt_out                          false
% 2.58/1.03  --trig_cnt_out_tolerance                1.
% 2.58/1.03  --trig_cnt_out_sk_spl                   false
% 2.58/1.03  --abstr_cl_out                          false
% 2.58/1.03  
% 2.58/1.03  ------ Global Options
% 2.58/1.03  
% 2.58/1.03  --schedule                              default
% 2.58/1.03  --add_important_lit                     false
% 2.58/1.03  --prop_solver_per_cl                    1000
% 2.58/1.03  --min_unsat_core                        false
% 2.58/1.03  --soft_assumptions                      false
% 2.58/1.03  --soft_lemma_size                       3
% 2.58/1.03  --prop_impl_unit_size                   0
% 2.58/1.03  --prop_impl_unit                        []
% 2.58/1.03  --share_sel_clauses                     true
% 2.58/1.03  --reset_solvers                         false
% 2.58/1.03  --bc_imp_inh                            [conj_cone]
% 2.58/1.03  --conj_cone_tolerance                   3.
% 2.58/1.03  --extra_neg_conj                        none
% 2.58/1.03  --large_theory_mode                     true
% 2.58/1.03  --prolific_symb_bound                   200
% 2.58/1.03  --lt_threshold                          2000
% 2.58/1.03  --clause_weak_htbl                      true
% 2.58/1.03  --gc_record_bc_elim                     false
% 2.58/1.03  
% 2.58/1.03  ------ Preprocessing Options
% 2.58/1.03  
% 2.58/1.03  --preprocessing_flag                    true
% 2.58/1.03  --time_out_prep_mult                    0.1
% 2.58/1.03  --splitting_mode                        input
% 2.58/1.03  --splitting_grd                         true
% 2.58/1.03  --splitting_cvd                         false
% 2.58/1.03  --splitting_cvd_svl                     false
% 2.58/1.03  --splitting_nvd                         32
% 2.58/1.03  --sub_typing                            true
% 2.58/1.03  --prep_gs_sim                           true
% 2.58/1.03  --prep_unflatten                        true
% 2.58/1.03  --prep_res_sim                          true
% 2.58/1.03  --prep_upred                            true
% 2.58/1.03  --prep_sem_filter                       exhaustive
% 2.58/1.03  --prep_sem_filter_out                   false
% 2.58/1.03  --pred_elim                             true
% 2.58/1.03  --res_sim_input                         true
% 2.58/1.03  --eq_ax_congr_red                       true
% 2.58/1.03  --pure_diseq_elim                       true
% 2.58/1.03  --brand_transform                       false
% 2.58/1.03  --non_eq_to_eq                          false
% 2.58/1.03  --prep_def_merge                        true
% 2.58/1.03  --prep_def_merge_prop_impl              false
% 2.58/1.03  --prep_def_merge_mbd                    true
% 2.58/1.03  --prep_def_merge_tr_red                 false
% 2.58/1.03  --prep_def_merge_tr_cl                  false
% 2.58/1.03  --smt_preprocessing                     true
% 2.58/1.03  --smt_ac_axioms                         fast
% 2.58/1.03  --preprocessed_out                      false
% 2.58/1.03  --preprocessed_stats                    false
% 2.58/1.03  
% 2.58/1.03  ------ Abstraction refinement Options
% 2.58/1.03  
% 2.58/1.03  --abstr_ref                             []
% 2.58/1.03  --abstr_ref_prep                        false
% 2.58/1.03  --abstr_ref_until_sat                   false
% 2.58/1.03  --abstr_ref_sig_restrict                funpre
% 2.58/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/1.03  --abstr_ref_under                       []
% 2.58/1.03  
% 2.58/1.03  ------ SAT Options
% 2.58/1.03  
% 2.58/1.03  --sat_mode                              false
% 2.58/1.03  --sat_fm_restart_options                ""
% 2.58/1.03  --sat_gr_def                            false
% 2.58/1.03  --sat_epr_types                         true
% 2.58/1.03  --sat_non_cyclic_types                  false
% 2.58/1.03  --sat_finite_models                     false
% 2.58/1.03  --sat_fm_lemmas                         false
% 2.58/1.03  --sat_fm_prep                           false
% 2.58/1.03  --sat_fm_uc_incr                        true
% 2.58/1.03  --sat_out_model                         small
% 2.58/1.03  --sat_out_clauses                       false
% 2.58/1.03  
% 2.58/1.03  ------ QBF Options
% 2.58/1.03  
% 2.58/1.03  --qbf_mode                              false
% 2.58/1.03  --qbf_elim_univ                         false
% 2.58/1.03  --qbf_dom_inst                          none
% 2.58/1.03  --qbf_dom_pre_inst                      false
% 2.58/1.03  --qbf_sk_in                             false
% 2.58/1.03  --qbf_pred_elim                         true
% 2.58/1.03  --qbf_split                             512
% 2.58/1.03  
% 2.58/1.03  ------ BMC1 Options
% 2.58/1.03  
% 2.58/1.03  --bmc1_incremental                      false
% 2.58/1.03  --bmc1_axioms                           reachable_all
% 2.58/1.03  --bmc1_min_bound                        0
% 2.58/1.03  --bmc1_max_bound                        -1
% 2.58/1.03  --bmc1_max_bound_default                -1
% 2.58/1.03  --bmc1_symbol_reachability              true
% 2.58/1.03  --bmc1_property_lemmas                  false
% 2.58/1.03  --bmc1_k_induction                      false
% 2.58/1.03  --bmc1_non_equiv_states                 false
% 2.58/1.03  --bmc1_deadlock                         false
% 2.58/1.03  --bmc1_ucm                              false
% 2.58/1.03  --bmc1_add_unsat_core                   none
% 2.58/1.03  --bmc1_unsat_core_children              false
% 2.58/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/1.03  --bmc1_out_stat                         full
% 2.58/1.03  --bmc1_ground_init                      false
% 2.58/1.03  --bmc1_pre_inst_next_state              false
% 2.58/1.03  --bmc1_pre_inst_state                   false
% 2.58/1.03  --bmc1_pre_inst_reach_state             false
% 2.58/1.03  --bmc1_out_unsat_core                   false
% 2.58/1.03  --bmc1_aig_witness_out                  false
% 2.58/1.03  --bmc1_verbose                          false
% 2.58/1.03  --bmc1_dump_clauses_tptp                false
% 2.58/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.58/1.03  --bmc1_dump_file                        -
% 2.58/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.58/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.58/1.03  --bmc1_ucm_extend_mode                  1
% 2.58/1.03  --bmc1_ucm_init_mode                    2
% 2.58/1.03  --bmc1_ucm_cone_mode                    none
% 2.58/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.58/1.03  --bmc1_ucm_relax_model                  4
% 2.58/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.58/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/1.03  --bmc1_ucm_layered_model                none
% 2.58/1.03  --bmc1_ucm_max_lemma_size               10
% 2.58/1.03  
% 2.58/1.03  ------ AIG Options
% 2.58/1.03  
% 2.58/1.03  --aig_mode                              false
% 2.58/1.03  
% 2.58/1.03  ------ Instantiation Options
% 2.58/1.03  
% 2.58/1.03  --instantiation_flag                    true
% 2.58/1.03  --inst_sos_flag                         false
% 2.58/1.03  --inst_sos_phase                        true
% 2.58/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/1.03  --inst_lit_sel_side                     num_symb
% 2.58/1.03  --inst_solver_per_active                1400
% 2.58/1.03  --inst_solver_calls_frac                1.
% 2.58/1.03  --inst_passive_queue_type               priority_queues
% 2.58/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/1.03  --inst_passive_queues_freq              [25;2]
% 2.58/1.03  --inst_dismatching                      true
% 2.58/1.03  --inst_eager_unprocessed_to_passive     true
% 2.58/1.03  --inst_prop_sim_given                   true
% 2.58/1.03  --inst_prop_sim_new                     false
% 2.58/1.03  --inst_subs_new                         false
% 2.58/1.03  --inst_eq_res_simp                      false
% 2.58/1.03  --inst_subs_given                       false
% 2.58/1.03  --inst_orphan_elimination               true
% 2.58/1.03  --inst_learning_loop_flag               true
% 2.58/1.03  --inst_learning_start                   3000
% 2.58/1.03  --inst_learning_factor                  2
% 2.58/1.03  --inst_start_prop_sim_after_learn       3
% 2.58/1.03  --inst_sel_renew                        solver
% 2.58/1.03  --inst_lit_activity_flag                true
% 2.58/1.03  --inst_restr_to_given                   false
% 2.58/1.03  --inst_activity_threshold               500
% 2.58/1.03  --inst_out_proof                        true
% 2.58/1.03  
% 2.58/1.03  ------ Resolution Options
% 2.58/1.03  
% 2.58/1.03  --resolution_flag                       true
% 2.58/1.03  --res_lit_sel                           adaptive
% 2.58/1.03  --res_lit_sel_side                      none
% 2.58/1.03  --res_ordering                          kbo
% 2.58/1.03  --res_to_prop_solver                    active
% 2.58/1.03  --res_prop_simpl_new                    false
% 2.58/1.03  --res_prop_simpl_given                  true
% 2.58/1.03  --res_passive_queue_type                priority_queues
% 2.58/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/1.03  --res_passive_queues_freq               [15;5]
% 2.58/1.03  --res_forward_subs                      full
% 2.58/1.03  --res_backward_subs                     full
% 2.58/1.03  --res_forward_subs_resolution           true
% 2.58/1.03  --res_backward_subs_resolution          true
% 2.58/1.03  --res_orphan_elimination                true
% 2.58/1.03  --res_time_limit                        2.
% 2.58/1.03  --res_out_proof                         true
% 2.58/1.03  
% 2.58/1.03  ------ Superposition Options
% 2.58/1.03  
% 2.58/1.03  --superposition_flag                    true
% 2.58/1.03  --sup_passive_queue_type                priority_queues
% 2.58/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.58/1.03  --demod_completeness_check              fast
% 2.58/1.03  --demod_use_ground                      true
% 2.58/1.03  --sup_to_prop_solver                    passive
% 2.58/1.03  --sup_prop_simpl_new                    true
% 2.58/1.03  --sup_prop_simpl_given                  true
% 2.58/1.03  --sup_fun_splitting                     false
% 2.58/1.03  --sup_smt_interval                      50000
% 2.58/1.03  
% 2.58/1.03  ------ Superposition Simplification Setup
% 2.58/1.03  
% 2.58/1.03  --sup_indices_passive                   []
% 2.58/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.03  --sup_full_bw                           [BwDemod]
% 2.58/1.03  --sup_immed_triv                        [TrivRules]
% 2.58/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.03  --sup_immed_bw_main                     []
% 2.58/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.03  
% 2.58/1.03  ------ Combination Options
% 2.58/1.03  
% 2.58/1.03  --comb_res_mult                         3
% 2.58/1.03  --comb_sup_mult                         2
% 2.58/1.03  --comb_inst_mult                        10
% 2.58/1.03  
% 2.58/1.03  ------ Debug Options
% 2.58/1.03  
% 2.58/1.03  --dbg_backtrace                         false
% 2.58/1.03  --dbg_dump_prop_clauses                 false
% 2.58/1.03  --dbg_dump_prop_clauses_file            -
% 2.58/1.03  --dbg_out_stat                          false
% 2.58/1.03  ------ Parsing...
% 2.58/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.58/1.03  
% 2.58/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.58/1.03  
% 2.58/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.58/1.03  
% 2.58/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.03  ------ Proving...
% 2.58/1.03  ------ Problem Properties 
% 2.58/1.03  
% 2.58/1.03  
% 2.58/1.03  clauses                                 27
% 2.58/1.03  conjectures                             4
% 2.58/1.03  EPR                                     4
% 2.58/1.03  Horn                                    22
% 2.58/1.03  unary                                   5
% 2.58/1.03  binary                                  10
% 2.58/1.03  lits                                    72
% 2.58/1.03  lits eq                                 9
% 2.58/1.03  fd_pure                                 0
% 2.58/1.03  fd_pseudo                               0
% 2.58/1.03  fd_cond                                 0
% 2.58/1.03  fd_pseudo_cond                          1
% 2.58/1.03  AC symbols                              0
% 2.58/1.03  
% 2.58/1.03  ------ Schedule dynamic 5 is on 
% 2.58/1.03  
% 2.58/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.58/1.03  
% 2.58/1.03  
% 2.58/1.03  ------ 
% 2.58/1.03  Current options:
% 2.58/1.03  ------ 
% 2.58/1.03  
% 2.58/1.03  ------ Input Options
% 2.58/1.03  
% 2.58/1.03  --out_options                           all
% 2.58/1.03  --tptp_safe_out                         true
% 2.58/1.03  --problem_path                          ""
% 2.58/1.03  --include_path                          ""
% 2.58/1.03  --clausifier                            res/vclausify_rel
% 2.58/1.03  --clausifier_options                    --mode clausify
% 2.58/1.03  --stdin                                 false
% 2.58/1.03  --stats_out                             all
% 2.58/1.03  
% 2.58/1.03  ------ General Options
% 2.58/1.03  
% 2.58/1.03  --fof                                   false
% 2.58/1.03  --time_out_real                         305.
% 2.58/1.03  --time_out_virtual                      -1.
% 2.58/1.03  --symbol_type_check                     false
% 2.58/1.03  --clausify_out                          false
% 2.58/1.03  --sig_cnt_out                           false
% 2.58/1.03  --trig_cnt_out                          false
% 2.58/1.03  --trig_cnt_out_tolerance                1.
% 2.58/1.03  --trig_cnt_out_sk_spl                   false
% 2.58/1.03  --abstr_cl_out                          false
% 2.58/1.03  
% 2.58/1.03  ------ Global Options
% 2.58/1.03  
% 2.58/1.03  --schedule                              default
% 2.58/1.03  --add_important_lit                     false
% 2.58/1.03  --prop_solver_per_cl                    1000
% 2.58/1.03  --min_unsat_core                        false
% 2.58/1.03  --soft_assumptions                      false
% 2.58/1.03  --soft_lemma_size                       3
% 2.58/1.03  --prop_impl_unit_size                   0
% 2.58/1.03  --prop_impl_unit                        []
% 2.58/1.03  --share_sel_clauses                     true
% 2.58/1.03  --reset_solvers                         false
% 2.58/1.03  --bc_imp_inh                            [conj_cone]
% 2.58/1.03  --conj_cone_tolerance                   3.
% 2.58/1.03  --extra_neg_conj                        none
% 2.58/1.03  --large_theory_mode                     true
% 2.58/1.03  --prolific_symb_bound                   200
% 2.58/1.03  --lt_threshold                          2000
% 2.58/1.03  --clause_weak_htbl                      true
% 2.58/1.03  --gc_record_bc_elim                     false
% 2.58/1.03  
% 2.58/1.03  ------ Preprocessing Options
% 2.58/1.03  
% 2.58/1.03  --preprocessing_flag                    true
% 2.58/1.03  --time_out_prep_mult                    0.1
% 2.58/1.03  --splitting_mode                        input
% 2.58/1.03  --splitting_grd                         true
% 2.58/1.03  --splitting_cvd                         false
% 2.58/1.03  --splitting_cvd_svl                     false
% 2.58/1.03  --splitting_nvd                         32
% 2.58/1.03  --sub_typing                            true
% 2.58/1.03  --prep_gs_sim                           true
% 2.58/1.03  --prep_unflatten                        true
% 2.58/1.03  --prep_res_sim                          true
% 2.58/1.03  --prep_upred                            true
% 2.58/1.03  --prep_sem_filter                       exhaustive
% 2.58/1.03  --prep_sem_filter_out                   false
% 2.58/1.03  --pred_elim                             true
% 2.58/1.03  --res_sim_input                         true
% 2.58/1.03  --eq_ax_congr_red                       true
% 2.58/1.03  --pure_diseq_elim                       true
% 2.58/1.03  --brand_transform                       false
% 2.58/1.03  --non_eq_to_eq                          false
% 2.58/1.03  --prep_def_merge                        true
% 2.58/1.03  --prep_def_merge_prop_impl              false
% 2.58/1.03  --prep_def_merge_mbd                    true
% 2.58/1.03  --prep_def_merge_tr_red                 false
% 2.58/1.03  --prep_def_merge_tr_cl                  false
% 2.58/1.03  --smt_preprocessing                     true
% 2.58/1.03  --smt_ac_axioms                         fast
% 2.58/1.03  --preprocessed_out                      false
% 2.58/1.03  --preprocessed_stats                    false
% 2.58/1.03  
% 2.58/1.03  ------ Abstraction refinement Options
% 2.58/1.03  
% 2.58/1.03  --abstr_ref                             []
% 2.58/1.03  --abstr_ref_prep                        false
% 2.58/1.03  --abstr_ref_until_sat                   false
% 2.58/1.03  --abstr_ref_sig_restrict                funpre
% 2.58/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/1.03  --abstr_ref_under                       []
% 2.58/1.03  
% 2.58/1.03  ------ SAT Options
% 2.58/1.03  
% 2.58/1.03  --sat_mode                              false
% 2.58/1.03  --sat_fm_restart_options                ""
% 2.58/1.03  --sat_gr_def                            false
% 2.58/1.03  --sat_epr_types                         true
% 2.58/1.03  --sat_non_cyclic_types                  false
% 2.58/1.03  --sat_finite_models                     false
% 2.58/1.03  --sat_fm_lemmas                         false
% 2.58/1.03  --sat_fm_prep                           false
% 2.58/1.03  --sat_fm_uc_incr                        true
% 2.58/1.03  --sat_out_model                         small
% 2.58/1.03  --sat_out_clauses                       false
% 2.58/1.03  
% 2.58/1.03  ------ QBF Options
% 2.58/1.03  
% 2.58/1.03  --qbf_mode                              false
% 2.58/1.03  --qbf_elim_univ                         false
% 2.58/1.03  --qbf_dom_inst                          none
% 2.58/1.03  --qbf_dom_pre_inst                      false
% 2.58/1.03  --qbf_sk_in                             false
% 2.58/1.03  --qbf_pred_elim                         true
% 2.58/1.03  --qbf_split                             512
% 2.58/1.03  
% 2.58/1.03  ------ BMC1 Options
% 2.58/1.03  
% 2.58/1.03  --bmc1_incremental                      false
% 2.58/1.03  --bmc1_axioms                           reachable_all
% 2.58/1.03  --bmc1_min_bound                        0
% 2.58/1.03  --bmc1_max_bound                        -1
% 2.58/1.03  --bmc1_max_bound_default                -1
% 2.58/1.03  --bmc1_symbol_reachability              true
% 2.58/1.03  --bmc1_property_lemmas                  false
% 2.58/1.03  --bmc1_k_induction                      false
% 2.58/1.03  --bmc1_non_equiv_states                 false
% 2.58/1.03  --bmc1_deadlock                         false
% 2.58/1.03  --bmc1_ucm                              false
% 2.58/1.03  --bmc1_add_unsat_core                   none
% 2.58/1.03  --bmc1_unsat_core_children              false
% 2.58/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/1.03  --bmc1_out_stat                         full
% 2.58/1.03  --bmc1_ground_init                      false
% 2.58/1.03  --bmc1_pre_inst_next_state              false
% 2.58/1.03  --bmc1_pre_inst_state                   false
% 2.58/1.03  --bmc1_pre_inst_reach_state             false
% 2.58/1.03  --bmc1_out_unsat_core                   false
% 2.58/1.03  --bmc1_aig_witness_out                  false
% 2.58/1.03  --bmc1_verbose                          false
% 2.58/1.03  --bmc1_dump_clauses_tptp                false
% 2.58/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.58/1.03  --bmc1_dump_file                        -
% 2.58/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.58/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.58/1.03  --bmc1_ucm_extend_mode                  1
% 2.58/1.03  --bmc1_ucm_init_mode                    2
% 2.58/1.03  --bmc1_ucm_cone_mode                    none
% 2.58/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.58/1.03  --bmc1_ucm_relax_model                  4
% 2.58/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.58/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/1.03  --bmc1_ucm_layered_model                none
% 2.58/1.03  --bmc1_ucm_max_lemma_size               10
% 2.58/1.03  
% 2.58/1.03  ------ AIG Options
% 2.58/1.03  
% 2.58/1.03  --aig_mode                              false
% 2.58/1.03  
% 2.58/1.03  ------ Instantiation Options
% 2.58/1.03  
% 2.58/1.03  --instantiation_flag                    true
% 2.58/1.03  --inst_sos_flag                         false
% 2.58/1.03  --inst_sos_phase                        true
% 2.58/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/1.03  --inst_lit_sel_side                     none
% 2.58/1.03  --inst_solver_per_active                1400
% 2.58/1.03  --inst_solver_calls_frac                1.
% 2.58/1.03  --inst_passive_queue_type               priority_queues
% 2.58/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/1.03  --inst_passive_queues_freq              [25;2]
% 2.58/1.03  --inst_dismatching                      true
% 2.58/1.03  --inst_eager_unprocessed_to_passive     true
% 2.58/1.03  --inst_prop_sim_given                   true
% 2.58/1.03  --inst_prop_sim_new                     false
% 2.58/1.03  --inst_subs_new                         false
% 2.58/1.03  --inst_eq_res_simp                      false
% 2.58/1.03  --inst_subs_given                       false
% 2.58/1.03  --inst_orphan_elimination               true
% 2.58/1.03  --inst_learning_loop_flag               true
% 2.58/1.03  --inst_learning_start                   3000
% 2.58/1.03  --inst_learning_factor                  2
% 2.58/1.03  --inst_start_prop_sim_after_learn       3
% 2.58/1.03  --inst_sel_renew                        solver
% 2.58/1.03  --inst_lit_activity_flag                true
% 2.58/1.03  --inst_restr_to_given                   false
% 2.58/1.03  --inst_activity_threshold               500
% 2.58/1.03  --inst_out_proof                        true
% 2.58/1.03  
% 2.58/1.03  ------ Resolution Options
% 2.58/1.03  
% 2.58/1.03  --resolution_flag                       false
% 2.58/1.03  --res_lit_sel                           adaptive
% 2.58/1.03  --res_lit_sel_side                      none
% 2.58/1.03  --res_ordering                          kbo
% 2.58/1.03  --res_to_prop_solver                    active
% 2.58/1.03  --res_prop_simpl_new                    false
% 2.58/1.03  --res_prop_simpl_given                  true
% 2.58/1.03  --res_passive_queue_type                priority_queues
% 2.58/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/1.03  --res_passive_queues_freq               [15;5]
% 2.58/1.03  --res_forward_subs                      full
% 2.58/1.03  --res_backward_subs                     full
% 2.58/1.03  --res_forward_subs_resolution           true
% 2.58/1.03  --res_backward_subs_resolution          true
% 2.58/1.03  --res_orphan_elimination                true
% 2.58/1.03  --res_time_limit                        2.
% 2.58/1.03  --res_out_proof                         true
% 2.58/1.03  
% 2.58/1.03  ------ Superposition Options
% 2.58/1.03  
% 2.58/1.03  --superposition_flag                    true
% 2.58/1.03  --sup_passive_queue_type                priority_queues
% 2.58/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.58/1.03  --demod_completeness_check              fast
% 2.58/1.03  --demod_use_ground                      true
% 2.58/1.03  --sup_to_prop_solver                    passive
% 2.58/1.03  --sup_prop_simpl_new                    true
% 2.58/1.03  --sup_prop_simpl_given                  true
% 2.58/1.03  --sup_fun_splitting                     false
% 2.58/1.03  --sup_smt_interval                      50000
% 2.58/1.03  
% 2.58/1.03  ------ Superposition Simplification Setup
% 2.58/1.03  
% 2.58/1.03  --sup_indices_passive                   []
% 2.58/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.03  --sup_full_bw                           [BwDemod]
% 2.58/1.03  --sup_immed_triv                        [TrivRules]
% 2.58/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.03  --sup_immed_bw_main                     []
% 2.58/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.03  
% 2.58/1.03  ------ Combination Options
% 2.58/1.03  
% 2.58/1.03  --comb_res_mult                         3
% 2.58/1.03  --comb_sup_mult                         2
% 2.58/1.03  --comb_inst_mult                        10
% 2.58/1.03  
% 2.58/1.03  ------ Debug Options
% 2.58/1.03  
% 2.58/1.03  --dbg_backtrace                         false
% 2.58/1.03  --dbg_dump_prop_clauses                 false
% 2.58/1.03  --dbg_dump_prop_clauses_file            -
% 2.58/1.03  --dbg_out_stat                          false
% 2.58/1.03  
% 2.58/1.03  
% 2.58/1.03  
% 2.58/1.03  
% 2.58/1.03  ------ Proving...
% 2.58/1.03  
% 2.58/1.03  
% 2.58/1.03  % SZS status Theorem for theBenchmark.p
% 2.58/1.03  
% 2.58/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.58/1.03  
% 2.58/1.03  fof(f15,conjecture,(
% 2.58/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.58/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.03  
% 2.58/1.03  fof(f16,negated_conjecture,(
% 2.58/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.58/1.03    inference(negated_conjecture,[],[f15])).
% 2.58/1.03  
% 2.58/1.03  fof(f31,plain,(
% 2.58/1.03    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.58/1.03    inference(ennf_transformation,[],[f16])).
% 2.58/1.03  
% 2.58/1.03  fof(f32,plain,(
% 2.58/1.03    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.58/1.03    inference(flattening,[],[f31])).
% 2.58/1.03  
% 2.58/1.03  fof(f48,plain,(
% 2.58/1.03    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK6,sK5),sK4) & k1_xboole_0 != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 2.58/1.03    introduced(choice_axiom,[])).
% 2.58/1.03  
% 2.58/1.03  fof(f49,plain,(
% 2.58/1.03    ~r2_hidden(k1_funct_1(sK6,sK5),sK4) & k1_xboole_0 != sK4 & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 2.58/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f32,f48])).
% 2.58/1.03  
% 2.58/1.03  fof(f79,plain,(
% 2.58/1.03    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.58/1.03    inference(cnf_transformation,[],[f49])).
% 2.58/1.03  
% 2.58/1.03  fof(f12,axiom,(
% 2.58/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.58/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.03  
% 2.58/1.03  fof(f27,plain,(
% 2.58/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.03    inference(ennf_transformation,[],[f12])).
% 2.58/1.03  
% 2.58/1.03  fof(f67,plain,(
% 2.58/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.03    inference(cnf_transformation,[],[f27])).
% 2.58/1.03  
% 2.58/1.03  fof(f14,axiom,(
% 2.58/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.58/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.03  
% 2.58/1.03  fof(f29,plain,(
% 2.58/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.03    inference(ennf_transformation,[],[f14])).
% 2.58/1.03  
% 2.58/1.03  fof(f30,plain,(
% 2.58/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.03    inference(flattening,[],[f29])).
% 2.58/1.03  
% 2.58/1.03  fof(f47,plain,(
% 2.58/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.03    inference(nnf_transformation,[],[f30])).
% 2.58/1.03  
% 2.58/1.03  fof(f71,plain,(
% 2.58/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.03    inference(cnf_transformation,[],[f47])).
% 2.58/1.03  
% 2.58/1.03  fof(f78,plain,(
% 2.58/1.03    v1_funct_2(sK6,sK3,sK4)),
% 2.58/1.03    inference(cnf_transformation,[],[f49])).
% 2.58/1.03  
% 2.58/1.03  fof(f81,plain,(
% 2.58/1.03    k1_xboole_0 != sK4),
% 2.58/1.03    inference(cnf_transformation,[],[f49])).
% 2.58/1.03  
% 2.58/1.03  fof(f10,axiom,(
% 2.58/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.58/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.03  
% 2.58/1.03  fof(f24,plain,(
% 2.58/1.03    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.58/1.03    inference(ennf_transformation,[],[f10])).
% 2.58/1.03  
% 2.58/1.03  fof(f25,plain,(
% 2.58/1.03    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.58/1.03    inference(flattening,[],[f24])).
% 2.58/1.03  
% 2.58/1.03  fof(f41,plain,(
% 2.58/1.03    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.58/1.03    inference(nnf_transformation,[],[f25])).
% 2.58/1.03  
% 2.58/1.03  fof(f42,plain,(
% 2.58/1.03    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.58/1.03    inference(flattening,[],[f41])).
% 2.58/1.03  
% 2.58/1.03  fof(f65,plain,(
% 2.58/1.03    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.58/1.03    inference(cnf_transformation,[],[f42])).
% 2.58/1.03  
% 2.58/1.03  fof(f83,plain,(
% 2.58/1.03    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.58/1.03    inference(equality_resolution,[],[f65])).
% 2.58/1.03  
% 2.58/1.03  fof(f77,plain,(
% 2.58/1.03    v1_funct_1(sK6)),
% 2.58/1.03    inference(cnf_transformation,[],[f49])).
% 2.58/1.03  
% 2.58/1.03  fof(f11,axiom,(
% 2.58/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.58/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.03  
% 2.58/1.03  fof(f26,plain,(
% 2.58/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.03    inference(ennf_transformation,[],[f11])).
% 2.58/1.03  
% 2.58/1.03  fof(f66,plain,(
% 2.58/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.03    inference(cnf_transformation,[],[f26])).
% 2.58/1.03  
% 2.58/1.03  fof(f6,axiom,(
% 2.58/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.58/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.03  
% 2.58/1.03  fof(f20,plain,(
% 2.58/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.58/1.03    inference(ennf_transformation,[],[f6])).
% 2.58/1.03  
% 2.58/1.03  fof(f59,plain,(
% 2.58/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.58/1.03    inference(cnf_transformation,[],[f20])).
% 2.58/1.03  
% 2.58/1.03  fof(f4,axiom,(
% 2.58/1.03    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.58/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.58/1.03  
% 2.58/1.03  fof(f37,plain,(
% 2.58/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.58/1.03    inference(nnf_transformation,[],[f4])).
% 2.58/1.03  
% 2.58/1.03  fof(f38,plain,(
% 2.58/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.58/1.03    inference(flattening,[],[f37])).
% 2.58/1.03  
% 2.58/1.03  fof(f55,plain,(
% 2.58/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.58/1.03    inference(cnf_transformation,[],[f38])).
% 2.58/1.03  
% 2.58/1.03  fof(f82,plain,(
% 2.58/1.03    ~r2_hidden(k1_funct_1(sK6,sK5),sK4)),
% 2.58/1.03    inference(cnf_transformation,[],[f49])).
% 2.58/1.03  
% 2.58/1.03  fof(f80,plain,(
% 2.58/1.03    r2_hidden(sK5,sK3)),
% 2.58/1.03    inference(cnf_transformation,[],[f49])).
% 2.58/1.03  
% 2.58/1.03  cnf(c_30,negated_conjecture,
% 2.58/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.58/1.03      inference(cnf_transformation,[],[f79]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_1203,plain,
% 2.58/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.58/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_17,plain,
% 2.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.58/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_1209,plain,
% 2.58/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.58/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.58/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_2919,plain,
% 2.58/1.03      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 2.58/1.03      inference(superposition,[status(thm)],[c_1203,c_1209]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_26,plain,
% 2.58/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.58/1.03      | k1_xboole_0 = X2 ),
% 2.58/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_31,negated_conjecture,
% 2.58/1.03      ( v1_funct_2(sK6,sK3,sK4) ),
% 2.58/1.03      inference(cnf_transformation,[],[f78]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_512,plain,
% 2.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.03      | k1_relset_1(X1,X2,X0) = X1
% 2.58/1.03      | sK3 != X1
% 2.58/1.03      | sK4 != X2
% 2.58/1.03      | sK6 != X0
% 2.58/1.03      | k1_xboole_0 = X2 ),
% 2.58/1.03      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_513,plain,
% 2.58/1.03      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.58/1.03      | k1_relset_1(sK3,sK4,sK6) = sK3
% 2.58/1.03      | k1_xboole_0 = sK4 ),
% 2.58/1.03      inference(unflattening,[status(thm)],[c_512]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_28,negated_conjecture,
% 2.58/1.03      ( k1_xboole_0 != sK4 ),
% 2.58/1.03      inference(cnf_transformation,[],[f81]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_515,plain,
% 2.58/1.03      ( k1_relset_1(sK3,sK4,sK6) = sK3 ),
% 2.58/1.03      inference(global_propositional_subsumption,
% 2.58/1.03                [status(thm)],
% 2.58/1.03                [c_513,c_30,c_28]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_2920,plain,
% 2.58/1.03      ( k1_relat_1(sK6) = sK3 ),
% 2.58/1.03      inference(light_normalisation,[status(thm)],[c_2919,c_515]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_13,plain,
% 2.58/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.58/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.58/1.03      | ~ v1_relat_1(X1)
% 2.58/1.03      | ~ v1_funct_1(X1) ),
% 2.58/1.03      inference(cnf_transformation,[],[f83]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_32,negated_conjecture,
% 2.58/1.03      ( v1_funct_1(sK6) ),
% 2.58/1.03      inference(cnf_transformation,[],[f77]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_371,plain,
% 2.58/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.58/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.58/1.03      | ~ v1_relat_1(X1)
% 2.58/1.03      | sK6 != X1 ),
% 2.58/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_372,plain,
% 2.58/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 2.58/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
% 2.58/1.03      | ~ v1_relat_1(sK6) ),
% 2.58/1.03      inference(unflattening,[status(thm)],[c_371]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_1201,plain,
% 2.58/1.03      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.58/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 2.58/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.58/1.03      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_35,plain,
% 2.58/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.58/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_373,plain,
% 2.58/1.03      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.58/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 2.58/1.03      | v1_relat_1(sK6) != iProver_top ),
% 2.58/1.03      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_16,plain,
% 2.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.03      | v1_relat_1(X0) ),
% 2.58/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_1433,plain,
% 2.58/1.03      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.58/1.03      | v1_relat_1(sK6) ),
% 2.58/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_1434,plain,
% 2.58/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.58/1.03      | v1_relat_1(sK6) = iProver_top ),
% 2.58/1.03      inference(predicate_to_equality,[status(thm)],[c_1433]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_1871,plain,
% 2.58/1.03      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 2.58/1.03      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 2.58/1.03      inference(global_propositional_subsumption,
% 2.58/1.03                [status(thm)],
% 2.58/1.03                [c_1201,c_35,c_373,c_1434]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_1872,plain,
% 2.58/1.03      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.58/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
% 2.58/1.03      inference(renaming,[status(thm)],[c_1871]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_3502,plain,
% 2.58/1.03      ( r2_hidden(X0,sK3) != iProver_top
% 2.58/1.03      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
% 2.58/1.03      inference(demodulation,[status(thm)],[c_2920,c_1872]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_9,plain,
% 2.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.58/1.03      | ~ r2_hidden(X2,X0)
% 2.58/1.03      | r2_hidden(X2,X1) ),
% 2.58/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_1214,plain,
% 2.58/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.58/1.03      | r2_hidden(X2,X0) != iProver_top
% 2.58/1.03      | r2_hidden(X2,X1) = iProver_top ),
% 2.58/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_4999,plain,
% 2.58/1.03      ( r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) = iProver_top
% 2.58/1.03      | r2_hidden(X0,sK6) != iProver_top ),
% 2.58/1.03      inference(superposition,[status(thm)],[c_1203,c_1214]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_5,plain,
% 2.58/1.03      ( r2_hidden(X0,X1)
% 2.58/1.03      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.58/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_1218,plain,
% 2.58/1.03      ( r2_hidden(X0,X1) = iProver_top
% 2.58/1.03      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 2.58/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_5087,plain,
% 2.58/1.03      ( r2_hidden(X0,sK4) = iProver_top
% 2.58/1.03      | r2_hidden(k4_tarski(X1,X0),sK6) != iProver_top ),
% 2.58/1.03      inference(superposition,[status(thm)],[c_4999,c_1218]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_5851,plain,
% 2.58/1.03      ( r2_hidden(X0,sK3) != iProver_top
% 2.58/1.03      | r2_hidden(k1_funct_1(sK6,X0),sK4) = iProver_top ),
% 2.58/1.03      inference(superposition,[status(thm)],[c_3502,c_5087]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_27,negated_conjecture,
% 2.58/1.03      ( ~ r2_hidden(k1_funct_1(sK6,sK5),sK4) ),
% 2.58/1.03      inference(cnf_transformation,[],[f82]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_1205,plain,
% 2.58/1.03      ( r2_hidden(k1_funct_1(sK6,sK5),sK4) != iProver_top ),
% 2.58/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_6300,plain,
% 2.58/1.03      ( r2_hidden(sK5,sK3) != iProver_top ),
% 2.58/1.03      inference(superposition,[status(thm)],[c_5851,c_1205]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_29,negated_conjecture,
% 2.58/1.03      ( r2_hidden(sK5,sK3) ),
% 2.58/1.03      inference(cnf_transformation,[],[f80]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(c_36,plain,
% 2.58/1.03      ( r2_hidden(sK5,sK3) = iProver_top ),
% 2.58/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.58/1.03  
% 2.58/1.03  cnf(contradiction,plain,
% 2.58/1.03      ( $false ),
% 2.58/1.03      inference(minisat,[status(thm)],[c_6300,c_36]) ).
% 2.58/1.03  
% 2.58/1.03  
% 2.58/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.58/1.03  
% 2.58/1.03  ------                               Statistics
% 2.58/1.03  
% 2.58/1.03  ------ General
% 2.58/1.03  
% 2.58/1.03  abstr_ref_over_cycles:                  0
% 2.58/1.03  abstr_ref_under_cycles:                 0
% 2.58/1.03  gc_basic_clause_elim:                   0
% 2.58/1.03  forced_gc_time:                         0
% 2.58/1.03  parsing_time:                           0.033
% 2.58/1.03  unif_index_cands_time:                  0.
% 2.58/1.03  unif_index_add_time:                    0.
% 2.58/1.03  orderings_time:                         0.
% 2.58/1.03  out_proof_time:                         0.009
% 2.58/1.03  total_time:                             0.302
% 2.58/1.03  num_of_symbols:                         51
% 2.58/1.03  num_of_terms:                           5262
% 2.58/1.03  
% 2.58/1.03  ------ Preprocessing
% 2.58/1.03  
% 2.58/1.03  num_of_splits:                          0
% 2.58/1.03  num_of_split_atoms:                     0
% 2.58/1.03  num_of_reused_defs:                     0
% 2.58/1.03  num_eq_ax_congr_red:                    22
% 2.58/1.03  num_of_sem_filtered_clauses:            1
% 2.58/1.03  num_of_subtypes:                        0
% 2.58/1.03  monotx_restored_types:                  0
% 2.58/1.03  sat_num_of_epr_types:                   0
% 2.58/1.03  sat_num_of_non_cyclic_types:            0
% 2.58/1.03  sat_guarded_non_collapsed_types:        0
% 2.58/1.03  num_pure_diseq_elim:                    0
% 2.58/1.03  simp_replaced_by:                       0
% 2.58/1.03  res_preprocessed:                       138
% 2.58/1.03  prep_upred:                             0
% 2.58/1.03  prep_unflattend:                        36
% 2.58/1.03  smt_new_axioms:                         0
% 2.58/1.03  pred_elim_cands:                        4
% 2.58/1.03  pred_elim:                              2
% 2.58/1.03  pred_elim_cl:                           5
% 2.58/1.03  pred_elim_cycles:                       5
% 2.58/1.03  merged_defs:                            0
% 2.58/1.03  merged_defs_ncl:                        0
% 2.58/1.03  bin_hyper_res:                          0
% 2.58/1.03  prep_cycles:                            4
% 2.58/1.03  pred_elim_time:                         0.018
% 2.58/1.03  splitting_time:                         0.
% 2.58/1.03  sem_filter_time:                        0.
% 2.58/1.03  monotx_time:                            0.
% 2.58/1.03  subtype_inf_time:                       0.
% 2.58/1.03  
% 2.58/1.03  ------ Problem properties
% 2.58/1.03  
% 2.58/1.03  clauses:                                27
% 2.58/1.03  conjectures:                            4
% 2.58/1.03  epr:                                    4
% 2.58/1.03  horn:                                   22
% 2.58/1.03  ground:                                 7
% 2.58/1.03  unary:                                  5
% 2.58/1.03  binary:                                 10
% 2.58/1.03  lits:                                   72
% 2.58/1.03  lits_eq:                                9
% 2.58/1.03  fd_pure:                                0
% 2.58/1.03  fd_pseudo:                              0
% 2.58/1.03  fd_cond:                                0
% 2.58/1.03  fd_pseudo_cond:                         1
% 2.58/1.03  ac_symbols:                             0
% 2.58/1.03  
% 2.58/1.03  ------ Propositional Solver
% 2.58/1.03  
% 2.58/1.03  prop_solver_calls:                      28
% 2.58/1.03  prop_fast_solver_calls:                 967
% 2.58/1.03  smt_solver_calls:                       0
% 2.58/1.03  smt_fast_solver_calls:                  0
% 2.58/1.03  prop_num_of_clauses:                    2790
% 2.58/1.03  prop_preprocess_simplified:             7897
% 2.58/1.03  prop_fo_subsumed:                       16
% 2.58/1.03  prop_solver_time:                       0.
% 2.58/1.03  smt_solver_time:                        0.
% 2.58/1.03  smt_fast_solver_time:                   0.
% 2.58/1.03  prop_fast_solver_time:                  0.
% 2.58/1.03  prop_unsat_core_time:                   0.
% 2.58/1.03  
% 2.58/1.03  ------ QBF
% 2.58/1.03  
% 2.58/1.03  qbf_q_res:                              0
% 2.58/1.03  qbf_num_tautologies:                    0
% 2.58/1.03  qbf_prep_cycles:                        0
% 2.58/1.03  
% 2.58/1.03  ------ BMC1
% 2.58/1.03  
% 2.58/1.03  bmc1_current_bound:                     -1
% 2.58/1.03  bmc1_last_solved_bound:                 -1
% 2.58/1.03  bmc1_unsat_core_size:                   -1
% 2.58/1.03  bmc1_unsat_core_parents_size:           -1
% 2.58/1.03  bmc1_merge_next_fun:                    0
% 2.58/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.58/1.03  
% 2.58/1.03  ------ Instantiation
% 2.58/1.03  
% 2.58/1.03  inst_num_of_clauses:                    852
% 2.58/1.03  inst_num_in_passive:                    397
% 2.58/1.03  inst_num_in_active:                     300
% 2.58/1.03  inst_num_in_unprocessed:                156
% 2.58/1.03  inst_num_of_loops:                      330
% 2.58/1.03  inst_num_of_learning_restarts:          0
% 2.58/1.03  inst_num_moves_active_passive:          26
% 2.58/1.03  inst_lit_activity:                      0
% 2.58/1.03  inst_lit_activity_moves:                1
% 2.58/1.03  inst_num_tautologies:                   0
% 2.58/1.03  inst_num_prop_implied:                  0
% 2.58/1.03  inst_num_existing_simplified:           0
% 2.58/1.03  inst_num_eq_res_simplified:             0
% 2.58/1.03  inst_num_child_elim:                    0
% 2.58/1.03  inst_num_of_dismatching_blockings:      23
% 2.58/1.03  inst_num_of_non_proper_insts:           487
% 2.58/1.03  inst_num_of_duplicates:                 0
% 2.58/1.03  inst_inst_num_from_inst_to_res:         0
% 2.58/1.03  inst_dismatching_checking_time:         0.
% 2.58/1.03  
% 2.58/1.03  ------ Resolution
% 2.58/1.03  
% 2.58/1.03  res_num_of_clauses:                     0
% 2.58/1.03  res_num_in_passive:                     0
% 2.58/1.03  res_num_in_active:                      0
% 2.58/1.03  res_num_of_loops:                       142
% 2.58/1.03  res_forward_subset_subsumed:            42
% 2.58/1.03  res_backward_subset_subsumed:           8
% 2.58/1.03  res_forward_subsumed:                   0
% 2.58/1.03  res_backward_subsumed:                  0
% 2.58/1.03  res_forward_subsumption_resolution:     0
% 2.58/1.03  res_backward_subsumption_resolution:    0
% 2.58/1.03  res_clause_to_clause_subsumption:       261
% 2.58/1.03  res_orphan_elimination:                 0
% 2.58/1.03  res_tautology_del:                      28
% 2.58/1.03  res_num_eq_res_simplified:              0
% 2.58/1.03  res_num_sel_changes:                    0
% 2.58/1.03  res_moves_from_active_to_pass:          0
% 2.58/1.03  
% 2.58/1.03  ------ Superposition
% 2.58/1.03  
% 2.58/1.03  sup_time_total:                         0.
% 2.58/1.03  sup_time_generating:                    0.
% 2.58/1.03  sup_time_sim_full:                      0.
% 2.58/1.03  sup_time_sim_immed:                     0.
% 2.58/1.03  
% 2.58/1.03  sup_num_of_clauses:                     84
% 2.58/1.03  sup_num_in_active:                      59
% 2.58/1.03  sup_num_in_passive:                     25
% 2.58/1.03  sup_num_of_loops:                       65
% 2.58/1.03  sup_fw_superposition:                   37
% 2.58/1.03  sup_bw_superposition:                   61
% 2.58/1.03  sup_immediate_simplified:               17
% 2.58/1.03  sup_given_eliminated:                   3
% 2.58/1.03  comparisons_done:                       0
% 2.58/1.03  comparisons_avoided:                    0
% 2.58/1.03  
% 2.58/1.03  ------ Simplifications
% 2.58/1.03  
% 2.58/1.03  
% 2.58/1.03  sim_fw_subset_subsumed:                 8
% 2.58/1.03  sim_bw_subset_subsumed:                 1
% 2.58/1.03  sim_fw_subsumed:                        5
% 2.58/1.03  sim_bw_subsumed:                        4
% 2.58/1.03  sim_fw_subsumption_res:                 2
% 2.58/1.03  sim_bw_subsumption_res:                 0
% 2.58/1.03  sim_tautology_del:                      8
% 2.58/1.03  sim_eq_tautology_del:                   2
% 2.58/1.03  sim_eq_res_simp:                        0
% 2.58/1.03  sim_fw_demodulated:                     0
% 2.58/1.03  sim_bw_demodulated:                     4
% 2.58/1.03  sim_light_normalised:                   5
% 2.58/1.03  sim_joinable_taut:                      0
% 2.58/1.03  sim_joinable_simp:                      0
% 2.58/1.03  sim_ac_normalised:                      0
% 2.58/1.03  sim_smt_subsumption:                    0
% 2.58/1.03  
%------------------------------------------------------------------------------
