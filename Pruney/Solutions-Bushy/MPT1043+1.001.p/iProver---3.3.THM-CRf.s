%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1043+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:45 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 884 expanded)
%              Number of clauses        :   62 ( 324 expanded)
%              Number of leaves         :   10 ( 168 expanded)
%              Depth                    :   23
%              Number of atoms          :  298 (2674 expanded)
%              Number of equality atoms :   98 ( 468 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26])).

fof(f42,plain,(
    ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X1)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(X3)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f33])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_166,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k5_partfun1(sK1,sK2,sK3) != X0
    | k1_funct_2(sK1,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_167,plain,
    ( r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)),k5_partfun1(sK1,sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_166])).

cnf(c_598,plain,
    ( r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)),k5_partfun1(sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_600,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X0,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_184,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_7,c_5])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_188,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_184,c_8,c_6])).

cnf(c_189,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(X1,X2))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_188])).

cnf(c_596,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
    | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_2,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_607,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_603,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_812,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_607,c_603])).

cnf(c_1497,plain,
    ( o_0_0_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,k5_partfun1(X2,X0,X1)) != iProver_top
    | r2_hidden(X3,k1_funct_2(X2,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_596,c_812])).

cnf(c_1504,plain,
    ( sK2 = o_0_0_xboole_0
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_600,c_1497])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1672,plain,
    ( r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | sK2 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1504,c_15])).

cnf(c_1673,plain,
    ( sK2 = o_0_0_xboole_0
    | r2_hidden(X0,k5_partfun1(sK1,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(sK1,sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1672])).

cnf(c_1681,plain,
    ( sK2 = o_0_0_xboole_0
    | r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)),k1_funct_2(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_1673])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_173,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k5_partfun1(sK1,sK2,sK3) != X0
    | k1_funct_2(sK1,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_174,plain,
    ( ~ r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)),k1_funct_2(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_175,plain,
    ( r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)),k1_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_1723,plain,
    ( sK2 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1681,c_175])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_606,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1534,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(k5_partfun1(sK1,sK2,sK3)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_600,c_606])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_602,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_995,plain,
    ( v1_xboole_0(k5_partfun1(sK1,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_602])).

cnf(c_1665,plain,
    ( v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1534,c_15,c_995])).

cnf(c_1726,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1723,c_1665])).

cnf(c_37,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1819,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1726,c_37])).

cnf(c_887,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_812,c_603])).

cnf(c_1825,plain,
    ( sK1 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1819,c_887])).

cnf(c_1734,plain,
    ( r2_hidden(sK0(k5_partfun1(sK1,o_0_0_xboole_0,sK3),k1_funct_2(sK1,o_0_0_xboole_0)),k5_partfun1(sK1,o_0_0_xboole_0,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1723,c_598])).

cnf(c_1971,plain,
    ( r2_hidden(sK0(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK3),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1825,c_1734])).

cnf(c_1736,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,o_0_0_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1723,c_600])).

cnf(c_1973,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1825,c_1736])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ r2_hidden(X5,k5_partfun1(X1,X2,X0))
    | r2_hidden(X3,k1_funct_2(k1_xboole_0,X4))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | X5 != X3
    | X2 != X4
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_7])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(X0,k5_partfun1(k1_xboole_0,X1,X2))
    | r2_hidden(X0,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_225,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0))
    | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
    | ~ v1_funct_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_209,c_8,c_6])).

cnf(c_595,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | r2_hidden(X2,k5_partfun1(k1_xboole_0,X1,X0)) != iProver_top
    | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_984,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) != iProver_top
    | r2_hidden(X2,k5_partfun1(o_0_0_xboole_0,X1,X0)) != iProver_top
    | r2_hidden(X2,k1_funct_2(o_0_0_xboole_0,X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_595,c_812])).

cnf(c_2062,plain,
    ( r2_hidden(X0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1973,c_984])).

cnf(c_2489,plain,
    ( r2_hidden(X0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top
    | r2_hidden(X0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2062,c_15])).

cnf(c_2490,plain,
    ( r2_hidden(X0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK3)) != iProver_top
    | r2_hidden(X0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2489])).

cnf(c_2497,plain,
    ( r2_hidden(sK0(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK3),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_2490])).

cnf(c_597,plain,
    ( r2_hidden(sK0(k5_partfun1(sK1,sK2,sK3),k1_funct_2(sK1,sK2)),k1_funct_2(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_1735,plain,
    ( r2_hidden(sK0(k5_partfun1(sK1,o_0_0_xboole_0,sK3),k1_funct_2(sK1,o_0_0_xboole_0)),k1_funct_2(sK1,o_0_0_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1723,c_597])).

cnf(c_1970,plain,
    ( r2_hidden(sK0(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK3),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1825,c_1735])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2497,c_1970])).


%------------------------------------------------------------------------------
