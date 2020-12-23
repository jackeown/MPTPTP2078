%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:38 EST 2020

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  107 (1743 expanded)
%              Number of clauses        :   78 ( 471 expanded)
%              Number of leaves         :   10 ( 476 expanded)
%              Depth                    :   17
%              Number of atoms          :  385 (11769 expanded)
%              Number of equality atoms :  132 ( 746 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,X1,sK2)
        & r1_partfun1(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X1,X2)
            & r1_partfun1(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,sK1,X2)
          & r1_partfun1(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    & r1_partfun1(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15,f14])).

fof(f25,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f21,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f6])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f19])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_7,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_215,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_216,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_8,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_218,plain,
    ( v1_partfun1(sK2,sK0)
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_216,c_8,c_6])).

cnf(c_316,plain,
    ( v1_partfun1(sK2,sK0)
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_218])).

cnf(c_486,plain,
    ( k1_xboole_0 = sK0
    | v1_partfun1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_229,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_230,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_232,plain,
    ( v1_partfun1(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_230,c_11,c_9])).

cnf(c_315,plain,
    ( v1_partfun1(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_232])).

cnf(c_322,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_480,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_3,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,negated_conjecture,
    ( r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_148,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | X0 = X2
    | sK2 != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_5])).

cnf(c_149,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | sK2 = sK1 ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_153,plain,
    ( ~ v1_partfun1(sK2,X0)
    | ~ v1_partfun1(sK1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | sK2 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_149,c_11,c_8])).

cnf(c_319,plain,
    ( ~ v1_partfun1(sK2,X0_41)
    | ~ v1_partfun1(sK1,X0_41)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41)))
    | sK2 = sK1 ),
    inference(subtyping,[status(esa)],[c_153])).

cnf(c_483,plain,
    ( sK2 = sK1
    | v1_partfun1(sK2,X0_41) != iProver_top
    | v1_partfun1(sK1,X0_41) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_324,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_339,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_0,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_127,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK2 != X3
    | sK1 != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 != sK2 ),
    inference(unflattening,[status(thm)],[c_127])).

cnf(c_132,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_128,c_6])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 != sK2 ),
    inference(subtyping,[status(esa)],[c_132])).

cnf(c_346,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 != sK2 ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_348,plain,
    ( sK2 = sK1
    | v1_partfun1(sK2,X0_41) != iProver_top
    | v1_partfun1(sK1,X0_41) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_328,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_555,plain,
    ( sK2 != X0_40
    | sK1 != X0_40
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_556,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_606,plain,
    ( v1_partfun1(sK2,X0_41) != iProver_top
    | v1_partfun1(sK1,X0_41) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_9,c_339,c_346,c_348,c_556])).

cnf(c_616,plain,
    ( v1_partfun1(sK2,sK0) != iProver_top
    | v1_partfun1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_480,c_606])).

cnf(c_617,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_616])).

cnf(c_674,plain,
    ( k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_9,c_6,c_339,c_346,c_349,c_316,c_315,c_556])).

cnf(c_14,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_667,plain,
    ( v1_partfun1(sK1,sK0) != iProver_top
    | v1_partfun1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_14])).

cnf(c_668,plain,
    ( v1_partfun1(sK2,sK0) != iProver_top
    | v1_partfun1(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_667])).

cnf(c_677,plain,
    ( v1_partfun1(sK2,k1_xboole_0) != iProver_top
    | v1_partfun1(sK1,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_674,c_668])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_198,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_199,plain,
    ( v1_partfun1(sK1,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(sK1)
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_201,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | v1_partfun1(sK1,k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_199,c_11])).

cnf(c_202,plain,
    ( v1_partfun1(sK1,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_317,plain,
    ( v1_partfun1(sK1,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_485,plain,
    ( sK0 != k1_xboole_0
    | v1_partfun1(sK1,k1_xboole_0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_325,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_340,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_349,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 = sK1 ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_352,plain,
    ( sK0 != k1_xboole_0
    | v1_partfun1(sK1,k1_xboole_0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_329,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_557,plain,
    ( sK0 != X0_41
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0_41 ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_558,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_557])).

cnf(c_599,plain,
    ( v1_partfun1(sK1,k1_xboole_0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_9,c_6,c_339,c_340,c_346,c_349,c_352,c_316,c_315,c_556,c_558])).

cnf(c_678,plain,
    ( v1_partfun1(sK1,k1_xboole_0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_674,c_599])).

cnf(c_321,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_481,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_680,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_674,c_481])).

cnf(c_692,plain,
    ( v1_partfun1(sK1,k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_678,c_680])).

cnf(c_181,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK0 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_182,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(sK2)
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_184,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | v1_partfun1(sK2,k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_182,c_8])).

cnf(c_185,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_318,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_185])).

cnf(c_484,plain,
    ( sK0 != k1_xboole_0
    | v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_351,plain,
    ( sK0 != k1_xboole_0
    | v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_571,plain,
    ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_9,c_6,c_339,c_340,c_346,c_349,c_351,c_316,c_315,c_556,c_558])).

cnf(c_679,plain,
    ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_674,c_571])).

cnf(c_681,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_674,c_480])).

cnf(c_688,plain,
    ( v1_partfun1(sK2,k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_679,c_681])).

cnf(c_696,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_677,c_692,c_688])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.10  % Command    : iproveropt_run.sh %d %s
% 0.10/0.31  % Computer   : n020.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 16:23:22 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running in FOF mode
% 0.81/0.93  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.81/0.93  
% 0.81/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.81/0.93  
% 0.81/0.93  ------  iProver source info
% 0.81/0.93  
% 0.81/0.93  git: date: 2020-06-30 10:37:57 +0100
% 0.81/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.81/0.93  git: non_committed_changes: false
% 0.81/0.93  git: last_make_outside_of_git: false
% 0.81/0.93  
% 0.81/0.93  ------ 
% 0.81/0.93  
% 0.81/0.93  ------ Input Options
% 0.81/0.93  
% 0.81/0.93  --out_options                           all
% 0.81/0.93  --tptp_safe_out                         true
% 0.81/0.93  --problem_path                          ""
% 0.81/0.93  --include_path                          ""
% 0.81/0.93  --clausifier                            res/vclausify_rel
% 0.81/0.93  --clausifier_options                    --mode clausify
% 0.81/0.93  --stdin                                 false
% 0.81/0.93  --stats_out                             all
% 0.81/0.93  
% 0.81/0.93  ------ General Options
% 0.81/0.93  
% 0.81/0.93  --fof                                   false
% 0.81/0.93  --time_out_real                         305.
% 0.81/0.93  --time_out_virtual                      -1.
% 0.81/0.93  --symbol_type_check                     false
% 0.81/0.93  --clausify_out                          false
% 0.81/0.93  --sig_cnt_out                           false
% 0.81/0.93  --trig_cnt_out                          false
% 0.81/0.93  --trig_cnt_out_tolerance                1.
% 0.81/0.93  --trig_cnt_out_sk_spl                   false
% 0.81/0.93  --abstr_cl_out                          false
% 0.81/0.93  
% 0.81/0.93  ------ Global Options
% 0.81/0.93  
% 0.81/0.93  --schedule                              default
% 0.81/0.93  --add_important_lit                     false
% 0.81/0.93  --prop_solver_per_cl                    1000
% 0.81/0.93  --min_unsat_core                        false
% 0.81/0.93  --soft_assumptions                      false
% 0.81/0.93  --soft_lemma_size                       3
% 0.81/0.93  --prop_impl_unit_size                   0
% 0.81/0.93  --prop_impl_unit                        []
% 0.81/0.93  --share_sel_clauses                     true
% 0.81/0.93  --reset_solvers                         false
% 0.81/0.93  --bc_imp_inh                            [conj_cone]
% 0.81/0.93  --conj_cone_tolerance                   3.
% 0.81/0.93  --extra_neg_conj                        none
% 0.81/0.93  --large_theory_mode                     true
% 0.81/0.93  --prolific_symb_bound                   200
% 0.81/0.93  --lt_threshold                          2000
% 0.81/0.93  --clause_weak_htbl                      true
% 0.81/0.93  --gc_record_bc_elim                     false
% 0.81/0.93  
% 0.81/0.93  ------ Preprocessing Options
% 0.81/0.93  
% 0.81/0.93  --preprocessing_flag                    true
% 0.81/0.93  --time_out_prep_mult                    0.1
% 0.81/0.93  --splitting_mode                        input
% 0.81/0.93  --splitting_grd                         true
% 0.81/0.93  --splitting_cvd                         false
% 0.81/0.93  --splitting_cvd_svl                     false
% 0.81/0.93  --splitting_nvd                         32
% 0.81/0.93  --sub_typing                            true
% 0.81/0.93  --prep_gs_sim                           true
% 0.81/0.93  --prep_unflatten                        true
% 0.81/0.93  --prep_res_sim                          true
% 0.81/0.93  --prep_upred                            true
% 0.81/0.93  --prep_sem_filter                       exhaustive
% 0.81/0.93  --prep_sem_filter_out                   false
% 0.81/0.93  --pred_elim                             true
% 0.81/0.93  --res_sim_input                         true
% 0.81/0.93  --eq_ax_congr_red                       true
% 0.81/0.93  --pure_diseq_elim                       true
% 0.81/0.93  --brand_transform                       false
% 0.81/0.93  --non_eq_to_eq                          false
% 0.81/0.93  --prep_def_merge                        true
% 0.81/0.93  --prep_def_merge_prop_impl              false
% 0.81/0.93  --prep_def_merge_mbd                    true
% 0.81/0.93  --prep_def_merge_tr_red                 false
% 0.81/0.93  --prep_def_merge_tr_cl                  false
% 0.81/0.93  --smt_preprocessing                     true
% 0.81/0.93  --smt_ac_axioms                         fast
% 0.81/0.93  --preprocessed_out                      false
% 0.81/0.93  --preprocessed_stats                    false
% 0.81/0.93  
% 0.81/0.93  ------ Abstraction refinement Options
% 0.81/0.93  
% 0.81/0.93  --abstr_ref                             []
% 0.81/0.93  --abstr_ref_prep                        false
% 0.81/0.93  --abstr_ref_until_sat                   false
% 0.81/0.93  --abstr_ref_sig_restrict                funpre
% 0.81/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 0.81/0.93  --abstr_ref_under                       []
% 0.81/0.93  
% 0.81/0.93  ------ SAT Options
% 0.81/0.93  
% 0.81/0.93  --sat_mode                              false
% 0.81/0.93  --sat_fm_restart_options                ""
% 0.81/0.93  --sat_gr_def                            false
% 0.81/0.93  --sat_epr_types                         true
% 0.81/0.93  --sat_non_cyclic_types                  false
% 0.81/0.93  --sat_finite_models                     false
% 0.81/0.93  --sat_fm_lemmas                         false
% 0.81/0.93  --sat_fm_prep                           false
% 0.81/0.93  --sat_fm_uc_incr                        true
% 0.81/0.93  --sat_out_model                         small
% 0.81/0.93  --sat_out_clauses                       false
% 0.81/0.93  
% 0.81/0.93  ------ QBF Options
% 0.81/0.93  
% 0.81/0.93  --qbf_mode                              false
% 0.81/0.93  --qbf_elim_univ                         false
% 0.81/0.93  --qbf_dom_inst                          none
% 0.81/0.93  --qbf_dom_pre_inst                      false
% 0.81/0.93  --qbf_sk_in                             false
% 0.81/0.93  --qbf_pred_elim                         true
% 0.81/0.93  --qbf_split                             512
% 0.81/0.93  
% 0.81/0.93  ------ BMC1 Options
% 0.81/0.93  
% 0.81/0.93  --bmc1_incremental                      false
% 0.81/0.93  --bmc1_axioms                           reachable_all
% 0.81/0.93  --bmc1_min_bound                        0
% 0.81/0.93  --bmc1_max_bound                        -1
% 0.81/0.93  --bmc1_max_bound_default                -1
% 0.81/0.93  --bmc1_symbol_reachability              true
% 0.81/0.93  --bmc1_property_lemmas                  false
% 0.81/0.93  --bmc1_k_induction                      false
% 0.81/0.93  --bmc1_non_equiv_states                 false
% 0.81/0.93  --bmc1_deadlock                         false
% 0.81/0.93  --bmc1_ucm                              false
% 0.81/0.93  --bmc1_add_unsat_core                   none
% 0.81/0.93  --bmc1_unsat_core_children              false
% 0.81/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 0.81/0.93  --bmc1_out_stat                         full
% 0.81/0.93  --bmc1_ground_init                      false
% 0.81/0.93  --bmc1_pre_inst_next_state              false
% 0.81/0.93  --bmc1_pre_inst_state                   false
% 0.81/0.93  --bmc1_pre_inst_reach_state             false
% 0.81/0.93  --bmc1_out_unsat_core                   false
% 0.81/0.93  --bmc1_aig_witness_out                  false
% 0.81/0.93  --bmc1_verbose                          false
% 0.81/0.93  --bmc1_dump_clauses_tptp                false
% 0.81/0.93  --bmc1_dump_unsat_core_tptp             false
% 0.81/0.93  --bmc1_dump_file                        -
% 0.81/0.93  --bmc1_ucm_expand_uc_limit              128
% 0.81/0.93  --bmc1_ucm_n_expand_iterations          6
% 0.81/0.93  --bmc1_ucm_extend_mode                  1
% 0.81/0.93  --bmc1_ucm_init_mode                    2
% 0.81/0.93  --bmc1_ucm_cone_mode                    none
% 0.81/0.93  --bmc1_ucm_reduced_relation_type        0
% 0.81/0.93  --bmc1_ucm_relax_model                  4
% 0.81/0.93  --bmc1_ucm_full_tr_after_sat            true
% 0.81/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 0.81/0.93  --bmc1_ucm_layered_model                none
% 0.81/0.93  --bmc1_ucm_max_lemma_size               10
% 0.81/0.93  
% 0.81/0.93  ------ AIG Options
% 0.81/0.93  
% 0.81/0.93  --aig_mode                              false
% 0.81/0.93  
% 0.81/0.93  ------ Instantiation Options
% 0.81/0.93  
% 0.81/0.93  --instantiation_flag                    true
% 0.81/0.93  --inst_sos_flag                         false
% 0.81/0.93  --inst_sos_phase                        true
% 0.81/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.81/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.81/0.93  --inst_lit_sel_side                     num_symb
% 0.81/0.93  --inst_solver_per_active                1400
% 0.81/0.93  --inst_solver_calls_frac                1.
% 0.81/0.93  --inst_passive_queue_type               priority_queues
% 0.81/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.81/0.93  --inst_passive_queues_freq              [25;2]
% 0.81/0.93  --inst_dismatching                      true
% 0.81/0.93  --inst_eager_unprocessed_to_passive     true
% 0.81/0.93  --inst_prop_sim_given                   true
% 0.81/0.93  --inst_prop_sim_new                     false
% 0.81/0.93  --inst_subs_new                         false
% 0.81/0.93  --inst_eq_res_simp                      false
% 0.81/0.93  --inst_subs_given                       false
% 0.81/0.93  --inst_orphan_elimination               true
% 0.81/0.93  --inst_learning_loop_flag               true
% 0.81/0.93  --inst_learning_start                   3000
% 0.81/0.93  --inst_learning_factor                  2
% 0.81/0.93  --inst_start_prop_sim_after_learn       3
% 0.81/0.93  --inst_sel_renew                        solver
% 0.81/0.93  --inst_lit_activity_flag                true
% 0.81/0.93  --inst_restr_to_given                   false
% 0.81/0.93  --inst_activity_threshold               500
% 0.81/0.93  --inst_out_proof                        true
% 0.81/0.93  
% 0.81/0.93  ------ Resolution Options
% 0.81/0.93  
% 0.81/0.93  --resolution_flag                       true
% 0.81/0.93  --res_lit_sel                           adaptive
% 0.81/0.93  --res_lit_sel_side                      none
% 0.81/0.93  --res_ordering                          kbo
% 0.81/0.93  --res_to_prop_solver                    active
% 0.81/0.93  --res_prop_simpl_new                    false
% 0.81/0.93  --res_prop_simpl_given                  true
% 0.81/0.93  --res_passive_queue_type                priority_queues
% 0.81/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.81/0.93  --res_passive_queues_freq               [15;5]
% 0.81/0.93  --res_forward_subs                      full
% 0.81/0.93  --res_backward_subs                     full
% 0.81/0.93  --res_forward_subs_resolution           true
% 0.81/0.93  --res_backward_subs_resolution          true
% 0.81/0.93  --res_orphan_elimination                true
% 0.81/0.93  --res_time_limit                        2.
% 0.81/0.93  --res_out_proof                         true
% 0.81/0.93  
% 0.81/0.93  ------ Superposition Options
% 0.81/0.93  
% 0.81/0.93  --superposition_flag                    true
% 0.81/0.93  --sup_passive_queue_type                priority_queues
% 0.81/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.81/0.93  --sup_passive_queues_freq               [8;1;4]
% 0.81/0.93  --demod_completeness_check              fast
% 0.81/0.93  --demod_use_ground                      true
% 0.81/0.93  --sup_to_prop_solver                    passive
% 0.81/0.93  --sup_prop_simpl_new                    true
% 0.81/0.93  --sup_prop_simpl_given                  true
% 0.81/0.93  --sup_fun_splitting                     false
% 0.81/0.93  --sup_smt_interval                      50000
% 0.81/0.93  
% 0.81/0.93  ------ Superposition Simplification Setup
% 0.81/0.93  
% 0.81/0.93  --sup_indices_passive                   []
% 0.81/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 0.81/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.93  --sup_full_bw                           [BwDemod]
% 0.81/0.93  --sup_immed_triv                        [TrivRules]
% 0.81/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.81/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.93  --sup_immed_bw_main                     []
% 0.81/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 0.81/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.93  
% 0.81/0.93  ------ Combination Options
% 0.81/0.93  
% 0.81/0.93  --comb_res_mult                         3
% 0.81/0.93  --comb_sup_mult                         2
% 0.81/0.93  --comb_inst_mult                        10
% 0.81/0.93  
% 0.81/0.93  ------ Debug Options
% 0.81/0.93  
% 0.81/0.93  --dbg_backtrace                         false
% 0.81/0.93  --dbg_dump_prop_clauses                 false
% 0.81/0.93  --dbg_dump_prop_clauses_file            -
% 0.81/0.93  --dbg_out_stat                          false
% 0.81/0.93  ------ Parsing...
% 0.81/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.81/0.93  
% 0.81/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 0.81/0.93  
% 0.81/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.81/0.93  
% 0.81/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.81/0.93  ------ Proving...
% 0.81/0.93  ------ Problem Properties 
% 0.81/0.93  
% 0.81/0.93  
% 0.81/0.93  clauses                                 8
% 0.81/0.93  conjectures                             2
% 0.81/0.93  EPR                                     2
% 0.81/0.93  Horn                                    6
% 0.81/0.93  unary                                   2
% 0.81/0.93  binary                                  3
% 0.81/0.93  lits                                    19
% 0.81/0.93  lits eq                                 6
% 0.81/0.93  fd_pure                                 0
% 0.81/0.93  fd_pseudo                               0
% 0.81/0.93  fd_cond                                 0
% 0.81/0.93  fd_pseudo_cond                          0
% 0.81/0.93  AC symbols                              0
% 0.81/0.93  
% 0.81/0.93  ------ Schedule dynamic 5 is on 
% 0.81/0.93  
% 0.81/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.81/0.93  
% 0.81/0.93  
% 0.81/0.93  ------ 
% 0.81/0.93  Current options:
% 0.81/0.93  ------ 
% 0.81/0.93  
% 0.81/0.93  ------ Input Options
% 0.81/0.93  
% 0.81/0.93  --out_options                           all
% 0.81/0.93  --tptp_safe_out                         true
% 0.81/0.93  --problem_path                          ""
% 0.81/0.93  --include_path                          ""
% 0.81/0.93  --clausifier                            res/vclausify_rel
% 0.81/0.93  --clausifier_options                    --mode clausify
% 0.81/0.93  --stdin                                 false
% 0.81/0.93  --stats_out                             all
% 0.81/0.93  
% 0.81/0.93  ------ General Options
% 0.81/0.93  
% 0.81/0.93  --fof                                   false
% 0.81/0.93  --time_out_real                         305.
% 0.81/0.93  --time_out_virtual                      -1.
% 0.81/0.93  --symbol_type_check                     false
% 0.81/0.93  --clausify_out                          false
% 0.81/0.93  --sig_cnt_out                           false
% 0.81/0.93  --trig_cnt_out                          false
% 0.81/0.93  --trig_cnt_out_tolerance                1.
% 0.81/0.93  --trig_cnt_out_sk_spl                   false
% 0.81/0.93  --abstr_cl_out                          false
% 0.81/0.93  
% 0.81/0.93  ------ Global Options
% 0.81/0.93  
% 0.81/0.93  --schedule                              default
% 0.81/0.93  --add_important_lit                     false
% 0.81/0.93  --prop_solver_per_cl                    1000
% 0.81/0.93  --min_unsat_core                        false
% 0.81/0.93  --soft_assumptions                      false
% 0.81/0.93  --soft_lemma_size                       3
% 0.81/0.93  --prop_impl_unit_size                   0
% 0.81/0.93  --prop_impl_unit                        []
% 0.81/0.93  --share_sel_clauses                     true
% 0.81/0.93  --reset_solvers                         false
% 0.81/0.93  --bc_imp_inh                            [conj_cone]
% 0.81/0.93  --conj_cone_tolerance                   3.
% 0.81/0.93  --extra_neg_conj                        none
% 0.81/0.93  --large_theory_mode                     true
% 0.81/0.93  --prolific_symb_bound                   200
% 0.81/0.93  --lt_threshold                          2000
% 0.81/0.93  --clause_weak_htbl                      true
% 0.81/0.93  --gc_record_bc_elim                     false
% 0.81/0.93  
% 0.81/0.93  ------ Preprocessing Options
% 0.81/0.93  
% 0.81/0.93  --preprocessing_flag                    true
% 0.81/0.93  --time_out_prep_mult                    0.1
% 0.81/0.93  --splitting_mode                        input
% 0.81/0.93  --splitting_grd                         true
% 0.81/0.93  --splitting_cvd                         false
% 0.81/0.93  --splitting_cvd_svl                     false
% 0.81/0.93  --splitting_nvd                         32
% 0.81/0.93  --sub_typing                            true
% 0.81/0.93  --prep_gs_sim                           true
% 0.81/0.93  --prep_unflatten                        true
% 0.81/0.93  --prep_res_sim                          true
% 0.81/0.93  --prep_upred                            true
% 0.81/0.93  --prep_sem_filter                       exhaustive
% 0.81/0.93  --prep_sem_filter_out                   false
% 0.81/0.93  --pred_elim                             true
% 0.81/0.93  --res_sim_input                         true
% 0.81/0.93  --eq_ax_congr_red                       true
% 0.81/0.93  --pure_diseq_elim                       true
% 0.81/0.93  --brand_transform                       false
% 0.81/0.93  --non_eq_to_eq                          false
% 0.81/0.93  --prep_def_merge                        true
% 0.81/0.93  --prep_def_merge_prop_impl              false
% 0.81/0.93  --prep_def_merge_mbd                    true
% 0.81/0.93  --prep_def_merge_tr_red                 false
% 0.81/0.93  --prep_def_merge_tr_cl                  false
% 0.81/0.93  --smt_preprocessing                     true
% 0.81/0.93  --smt_ac_axioms                         fast
% 0.81/0.93  --preprocessed_out                      false
% 0.81/0.93  --preprocessed_stats                    false
% 0.81/0.93  
% 0.81/0.93  ------ Abstraction refinement Options
% 0.81/0.93  
% 0.81/0.93  --abstr_ref                             []
% 0.81/0.93  --abstr_ref_prep                        false
% 0.81/0.93  --abstr_ref_until_sat                   false
% 0.81/0.93  --abstr_ref_sig_restrict                funpre
% 0.81/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 0.81/0.93  --abstr_ref_under                       []
% 0.81/0.93  
% 0.81/0.93  ------ SAT Options
% 0.81/0.93  
% 0.81/0.93  --sat_mode                              false
% 0.81/0.93  --sat_fm_restart_options                ""
% 0.81/0.93  --sat_gr_def                            false
% 0.81/0.93  --sat_epr_types                         true
% 0.81/0.93  --sat_non_cyclic_types                  false
% 0.81/0.93  --sat_finite_models                     false
% 0.81/0.93  --sat_fm_lemmas                         false
% 0.81/0.93  --sat_fm_prep                           false
% 0.81/0.93  --sat_fm_uc_incr                        true
% 0.81/0.93  --sat_out_model                         small
% 0.81/0.93  --sat_out_clauses                       false
% 0.81/0.93  
% 0.81/0.93  ------ QBF Options
% 0.81/0.93  
% 0.81/0.93  --qbf_mode                              false
% 0.81/0.93  --qbf_elim_univ                         false
% 0.81/0.93  --qbf_dom_inst                          none
% 0.81/0.93  --qbf_dom_pre_inst                      false
% 0.81/0.93  --qbf_sk_in                             false
% 0.81/0.93  --qbf_pred_elim                         true
% 0.81/0.93  --qbf_split                             512
% 0.81/0.93  
% 0.81/0.93  ------ BMC1 Options
% 0.81/0.93  
% 0.81/0.93  --bmc1_incremental                      false
% 0.81/0.93  --bmc1_axioms                           reachable_all
% 0.81/0.93  --bmc1_min_bound                        0
% 0.81/0.93  --bmc1_max_bound                        -1
% 0.81/0.93  --bmc1_max_bound_default                -1
% 0.81/0.93  --bmc1_symbol_reachability              true
% 0.81/0.93  --bmc1_property_lemmas                  false
% 0.81/0.93  --bmc1_k_induction                      false
% 0.81/0.93  --bmc1_non_equiv_states                 false
% 0.81/0.93  --bmc1_deadlock                         false
% 0.81/0.93  --bmc1_ucm                              false
% 0.81/0.93  --bmc1_add_unsat_core                   none
% 0.81/0.93  --bmc1_unsat_core_children              false
% 0.81/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 0.81/0.93  --bmc1_out_stat                         full
% 0.81/0.93  --bmc1_ground_init                      false
% 0.81/0.93  --bmc1_pre_inst_next_state              false
% 0.81/0.93  --bmc1_pre_inst_state                   false
% 0.81/0.93  --bmc1_pre_inst_reach_state             false
% 0.81/0.93  --bmc1_out_unsat_core                   false
% 0.81/0.93  --bmc1_aig_witness_out                  false
% 0.81/0.93  --bmc1_verbose                          false
% 0.81/0.93  --bmc1_dump_clauses_tptp                false
% 0.81/0.93  --bmc1_dump_unsat_core_tptp             false
% 0.81/0.93  --bmc1_dump_file                        -
% 0.81/0.93  --bmc1_ucm_expand_uc_limit              128
% 0.81/0.93  --bmc1_ucm_n_expand_iterations          6
% 0.81/0.93  --bmc1_ucm_extend_mode                  1
% 0.81/0.93  --bmc1_ucm_init_mode                    2
% 0.81/0.93  --bmc1_ucm_cone_mode                    none
% 0.81/0.93  --bmc1_ucm_reduced_relation_type        0
% 0.81/0.93  --bmc1_ucm_relax_model                  4
% 0.81/0.93  --bmc1_ucm_full_tr_after_sat            true
% 0.81/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 0.81/0.93  --bmc1_ucm_layered_model                none
% 0.81/0.93  --bmc1_ucm_max_lemma_size               10
% 0.81/0.93  
% 0.81/0.93  ------ AIG Options
% 0.81/0.93  
% 0.81/0.93  --aig_mode                              false
% 0.81/0.93  
% 0.81/0.93  ------ Instantiation Options
% 0.81/0.93  
% 0.81/0.93  --instantiation_flag                    true
% 0.81/0.93  --inst_sos_flag                         false
% 0.81/0.93  --inst_sos_phase                        true
% 0.81/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.81/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.81/0.93  --inst_lit_sel_side                     none
% 0.81/0.93  --inst_solver_per_active                1400
% 0.81/0.93  --inst_solver_calls_frac                1.
% 0.81/0.93  --inst_passive_queue_type               priority_queues
% 0.81/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.81/0.93  --inst_passive_queues_freq              [25;2]
% 0.81/0.93  --inst_dismatching                      true
% 0.81/0.93  --inst_eager_unprocessed_to_passive     true
% 0.81/0.93  --inst_prop_sim_given                   true
% 0.81/0.93  --inst_prop_sim_new                     false
% 0.81/0.93  --inst_subs_new                         false
% 0.81/0.93  --inst_eq_res_simp                      false
% 0.81/0.93  --inst_subs_given                       false
% 0.81/0.93  --inst_orphan_elimination               true
% 0.81/0.93  --inst_learning_loop_flag               true
% 0.81/0.93  --inst_learning_start                   3000
% 0.81/0.93  --inst_learning_factor                  2
% 0.81/0.93  --inst_start_prop_sim_after_learn       3
% 0.81/0.93  --inst_sel_renew                        solver
% 0.81/0.93  --inst_lit_activity_flag                true
% 0.81/0.93  --inst_restr_to_given                   false
% 0.81/0.93  --inst_activity_threshold               500
% 0.81/0.93  --inst_out_proof                        true
% 0.81/0.93  
% 0.81/0.93  ------ Resolution Options
% 0.81/0.93  
% 0.81/0.93  --resolution_flag                       false
% 0.81/0.93  --res_lit_sel                           adaptive
% 0.81/0.93  --res_lit_sel_side                      none
% 0.81/0.93  --res_ordering                          kbo
% 0.81/0.93  --res_to_prop_solver                    active
% 0.81/0.93  --res_prop_simpl_new                    false
% 0.81/0.93  --res_prop_simpl_given                  true
% 0.81/0.93  --res_passive_queue_type                priority_queues
% 0.81/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.81/0.93  --res_passive_queues_freq               [15;5]
% 0.81/0.93  --res_forward_subs                      full
% 0.81/0.93  --res_backward_subs                     full
% 0.81/0.93  --res_forward_subs_resolution           true
% 0.81/0.93  --res_backward_subs_resolution          true
% 0.81/0.93  --res_orphan_elimination                true
% 0.81/0.93  --res_time_limit                        2.
% 0.81/0.93  --res_out_proof                         true
% 0.81/0.93  
% 0.81/0.93  ------ Superposition Options
% 0.81/0.93  
% 0.81/0.93  --superposition_flag                    true
% 0.81/0.93  --sup_passive_queue_type                priority_queues
% 0.81/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.81/0.93  --sup_passive_queues_freq               [8;1;4]
% 0.81/0.93  --demod_completeness_check              fast
% 0.81/0.93  --demod_use_ground                      true
% 0.81/0.93  --sup_to_prop_solver                    passive
% 0.81/0.93  --sup_prop_simpl_new                    true
% 0.81/0.93  --sup_prop_simpl_given                  true
% 0.81/0.93  --sup_fun_splitting                     false
% 0.81/0.93  --sup_smt_interval                      50000
% 0.81/0.93  
% 0.81/0.93  ------ Superposition Simplification Setup
% 0.81/0.93  
% 0.81/0.93  --sup_indices_passive                   []
% 0.81/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 0.81/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.93  --sup_full_bw                           [BwDemod]
% 0.81/0.93  --sup_immed_triv                        [TrivRules]
% 0.81/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.81/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.93  --sup_immed_bw_main                     []
% 0.81/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 0.81/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.93  
% 0.81/0.93  ------ Combination Options
% 0.81/0.93  
% 0.81/0.93  --comb_res_mult                         3
% 0.81/0.93  --comb_sup_mult                         2
% 0.81/0.93  --comb_inst_mult                        10
% 0.81/0.93  
% 0.81/0.93  ------ Debug Options
% 0.81/0.93  
% 0.81/0.93  --dbg_backtrace                         false
% 0.81/0.93  --dbg_dump_prop_clauses                 false
% 0.81/0.93  --dbg_dump_prop_clauses_file            -
% 0.81/0.93  --dbg_out_stat                          false
% 0.81/0.93  
% 0.81/0.93  
% 0.81/0.93  
% 0.81/0.93  
% 0.81/0.93  ------ Proving...
% 0.81/0.93  
% 0.81/0.93  
% 0.81/0.93  % SZS status Theorem for theBenchmark.p
% 0.81/0.93  
% 0.81/0.93   Resolution empty clause
% 0.81/0.93  
% 0.81/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 0.81/0.93  
% 0.81/0.93  fof(f2,axiom,(
% 0.81/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.81/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.81/0.93  
% 0.81/0.93  fof(f8,plain,(
% 0.81/0.93    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.81/0.93    inference(ennf_transformation,[],[f2])).
% 0.81/0.93  
% 0.81/0.93  fof(f9,plain,(
% 0.81/0.93    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.81/0.93    inference(flattening,[],[f8])).
% 0.81/0.93  
% 0.81/0.93  fof(f18,plain,(
% 0.81/0.93    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.81/0.93    inference(cnf_transformation,[],[f9])).
% 0.81/0.93  
% 0.81/0.93  fof(f4,conjecture,(
% 0.81/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_relset_1(X0,X0,X1,X2))))),
% 0.81/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.81/0.93  
% 0.81/0.93  fof(f5,negated_conjecture,(
% 0.81/0.93    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_relset_1(X0,X0,X1,X2))))),
% 0.81/0.93    inference(negated_conjecture,[],[f4])).
% 0.81/0.93  
% 0.81/0.93  fof(f12,plain,(
% 0.81/0.93    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.81/0.93    inference(ennf_transformation,[],[f5])).
% 0.81/0.93  
% 0.81/0.93  fof(f13,plain,(
% 0.81/0.93    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.81/0.93    inference(flattening,[],[f12])).
% 0.81/0.93  
% 0.81/0.93  fof(f15,plain,(
% 0.81/0.93    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,X1,sK2) & r1_partfun1(X1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 0.81/0.93    introduced(choice_axiom,[])).
% 0.81/0.93  
% 0.81/0.93  fof(f14,plain,(
% 0.81/0.93    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,sK1,X2) & r1_partfun1(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.81/0.93    introduced(choice_axiom,[])).
% 0.81/0.93  
% 0.81/0.93  fof(f16,plain,(
% 0.81/0.93    (~r2_relset_1(sK0,sK0,sK1,sK2) & r1_partfun1(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.81/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15,f14])).
% 0.81/0.93  
% 0.81/0.93  fof(f25,plain,(
% 0.81/0.93    v1_funct_2(sK2,sK0,sK0)),
% 0.81/0.93    inference(cnf_transformation,[],[f16])).
% 0.81/0.93  
% 0.81/0.93  fof(f24,plain,(
% 0.81/0.93    v1_funct_1(sK2)),
% 0.81/0.93    inference(cnf_transformation,[],[f16])).
% 0.81/0.93  
% 0.81/0.93  fof(f26,plain,(
% 0.81/0.93    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.81/0.93    inference(cnf_transformation,[],[f16])).
% 0.81/0.93  
% 0.81/0.93  fof(f23,plain,(
% 0.81/0.93    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.81/0.93    inference(cnf_transformation,[],[f16])).
% 0.81/0.93  
% 0.81/0.93  fof(f22,plain,(
% 0.81/0.93    v1_funct_2(sK1,sK0,sK0)),
% 0.81/0.93    inference(cnf_transformation,[],[f16])).
% 0.81/0.93  
% 0.81/0.93  fof(f21,plain,(
% 0.81/0.93    v1_funct_1(sK1)),
% 0.81/0.93    inference(cnf_transformation,[],[f16])).
% 0.81/0.93  
% 0.81/0.93  fof(f3,axiom,(
% 0.81/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.81/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.81/0.93  
% 0.81/0.93  fof(f10,plain,(
% 0.81/0.93    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.81/0.93    inference(ennf_transformation,[],[f3])).
% 0.81/0.93  
% 0.81/0.93  fof(f11,plain,(
% 0.81/0.93    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.81/0.93    inference(flattening,[],[f10])).
% 0.81/0.93  
% 0.81/0.93  fof(f20,plain,(
% 0.81/0.93    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.81/0.93    inference(cnf_transformation,[],[f11])).
% 0.81/0.93  
% 0.81/0.93  fof(f27,plain,(
% 0.81/0.93    r1_partfun1(sK1,sK2)),
% 0.81/0.93    inference(cnf_transformation,[],[f16])).
% 0.81/0.93  
% 0.81/0.93  fof(f1,axiom,(
% 0.81/0.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.81/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.81/0.93  
% 0.81/0.93  fof(f6,plain,(
% 0.81/0.93    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.81/0.93    inference(ennf_transformation,[],[f1])).
% 0.81/0.93  
% 0.81/0.93  fof(f7,plain,(
% 0.81/0.93    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.81/0.93    inference(flattening,[],[f6])).
% 0.81/0.93  
% 0.81/0.93  fof(f17,plain,(
% 0.81/0.93    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.81/0.93    inference(cnf_transformation,[],[f7])).
% 0.81/0.93  
% 0.81/0.93  fof(f28,plain,(
% 0.81/0.93    ~r2_relset_1(sK0,sK0,sK1,sK2)),
% 0.81/0.93    inference(cnf_transformation,[],[f16])).
% 0.81/0.93  
% 0.81/0.93  fof(f19,plain,(
% 0.81/0.93    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.81/0.93    inference(cnf_transformation,[],[f9])).
% 0.81/0.93  
% 0.81/0.93  fof(f29,plain,(
% 0.81/0.93    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.81/0.93    inference(equality_resolution,[],[f19])).
% 0.81/0.93  
% 0.81/0.93  cnf(c_2,plain,
% 0.81/0.93      ( ~ v1_funct_2(X0,X1,X2)
% 0.81/0.93      | v1_partfun1(X0,X1)
% 0.81/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.81/0.93      | ~ v1_funct_1(X0)
% 0.81/0.93      | k1_xboole_0 = X2 ),
% 0.81/0.93      inference(cnf_transformation,[],[f18]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_7,negated_conjecture,
% 0.81/0.93      ( v1_funct_2(sK2,sK0,sK0) ),
% 0.81/0.93      inference(cnf_transformation,[],[f25]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_215,plain,
% 0.81/0.93      ( v1_partfun1(X0,X1)
% 0.81/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.81/0.93      | ~ v1_funct_1(X0)
% 0.81/0.93      | sK2 != X0
% 0.81/0.93      | sK0 != X1
% 0.81/0.93      | sK0 != X2
% 0.81/0.93      | k1_xboole_0 = X2 ),
% 0.81/0.93      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_216,plain,
% 0.81/0.93      ( v1_partfun1(sK2,sK0)
% 0.81/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.81/0.93      | ~ v1_funct_1(sK2)
% 0.81/0.93      | k1_xboole_0 = sK0 ),
% 0.81/0.93      inference(unflattening,[status(thm)],[c_215]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_8,negated_conjecture,
% 0.81/0.93      ( v1_funct_1(sK2) ),
% 0.81/0.93      inference(cnf_transformation,[],[f24]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_6,negated_conjecture,
% 0.81/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 0.81/0.93      inference(cnf_transformation,[],[f26]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_218,plain,
% 0.81/0.93      ( v1_partfun1(sK2,sK0) | k1_xboole_0 = sK0 ),
% 0.81/0.93      inference(global_propositional_subsumption,[status(thm)],[c_216,c_8,c_6]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_316,plain,
% 0.81/0.93      ( v1_partfun1(sK2,sK0) | k1_xboole_0 = sK0 ),
% 0.81/0.93      inference(subtyping,[status(esa)],[c_218]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_486,plain,
% 0.81/0.93      ( k1_xboole_0 = sK0 | v1_partfun1(sK2,sK0) = iProver_top ),
% 0.81/0.93      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_9,negated_conjecture,
% 0.81/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 0.81/0.93      inference(cnf_transformation,[],[f23]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_10,negated_conjecture,
% 0.81/0.93      ( v1_funct_2(sK1,sK0,sK0) ),
% 0.81/0.93      inference(cnf_transformation,[],[f22]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_229,plain,
% 0.81/0.93      ( v1_partfun1(X0,X1)
% 0.81/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.81/0.93      | ~ v1_funct_1(X0)
% 0.81/0.93      | sK1 != X0
% 0.81/0.93      | sK0 != X1
% 0.81/0.93      | sK0 != X2
% 0.81/0.93      | k1_xboole_0 = X2 ),
% 0.81/0.93      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_230,plain,
% 0.81/0.93      ( v1_partfun1(sK1,sK0)
% 0.81/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.81/0.93      | ~ v1_funct_1(sK1)
% 0.81/0.93      | k1_xboole_0 = sK0 ),
% 0.81/0.93      inference(unflattening,[status(thm)],[c_229]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_11,negated_conjecture,
% 0.81/0.93      ( v1_funct_1(sK1) ),
% 0.81/0.93      inference(cnf_transformation,[],[f21]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_232,plain,
% 0.81/0.93      ( v1_partfun1(sK1,sK0) | k1_xboole_0 = sK0 ),
% 0.81/0.93      inference(global_propositional_subsumption,
% 0.81/0.93                [status(thm)],
% 0.81/0.93                [c_230,c_11,c_9]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_315,plain,
% 0.81/0.93      ( v1_partfun1(sK1,sK0) | k1_xboole_0 = sK0 ),
% 0.81/0.93      inference(subtyping,[status(esa)],[c_232]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_322,negated_conjecture,
% 0.81/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 0.81/0.93      inference(subtyping,[status(esa)],[c_6]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_480,plain,
% 0.81/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 0.81/0.93      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_3,plain,
% 0.81/0.93      ( ~ r1_partfun1(X0,X1)
% 0.81/0.93      | ~ v1_partfun1(X1,X2)
% 0.81/0.93      | ~ v1_partfun1(X0,X2)
% 0.81/0.93      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 0.81/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 0.81/0.93      | ~ v1_funct_1(X0)
% 0.81/0.93      | ~ v1_funct_1(X1)
% 0.81/0.93      | X1 = X0 ),
% 0.81/0.93      inference(cnf_transformation,[],[f20]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_5,negated_conjecture,
% 0.81/0.93      ( r1_partfun1(sK1,sK2) ),
% 0.81/0.93      inference(cnf_transformation,[],[f27]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_148,plain,
% 0.81/0.93      ( ~ v1_partfun1(X0,X1)
% 0.81/0.93      | ~ v1_partfun1(X2,X1)
% 0.81/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 0.81/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 0.81/0.93      | ~ v1_funct_1(X2)
% 0.81/0.93      | ~ v1_funct_1(X0)
% 0.81/0.93      | X0 = X2
% 0.81/0.93      | sK2 != X0
% 0.81/0.93      | sK1 != X2 ),
% 0.81/0.93      inference(resolution_lifted,[status(thm)],[c_3,c_5]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_149,plain,
% 0.81/0.93      ( ~ v1_partfun1(sK2,X0)
% 0.81/0.93      | ~ v1_partfun1(sK1,X0)
% 0.81/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.81/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.81/0.93      | ~ v1_funct_1(sK2)
% 0.81/0.93      | ~ v1_funct_1(sK1)
% 0.81/0.93      | sK2 = sK1 ),
% 0.81/0.93      inference(unflattening,[status(thm)],[c_148]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_153,plain,
% 0.81/0.93      ( ~ v1_partfun1(sK2,X0)
% 0.81/0.93      | ~ v1_partfun1(sK1,X0)
% 0.81/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.81/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.81/0.93      | sK2 = sK1 ),
% 0.81/0.93      inference(global_propositional_subsumption,
% 0.81/0.93                [status(thm)],
% 0.81/0.93                [c_149,c_11,c_8]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_319,plain,
% 0.81/0.93      ( ~ v1_partfun1(sK2,X0_41)
% 0.81/0.93      | ~ v1_partfun1(sK1,X0_41)
% 0.81/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41)))
% 0.81/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41)))
% 0.81/0.93      | sK2 = sK1 ),
% 0.81/0.93      inference(subtyping,[status(esa)],[c_153]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_483,plain,
% 0.81/0.93      ( sK2 = sK1
% 0.81/0.93      | v1_partfun1(sK2,X0_41) != iProver_top
% 0.81/0.93      | v1_partfun1(sK1,X0_41) != iProver_top
% 0.81/0.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top
% 0.81/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top ),
% 0.81/0.93      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_324,plain,( X0_40 = X0_40 ),theory(equality) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_339,plain,
% 0.81/0.93      ( sK1 = sK1 ),
% 0.81/0.93      inference(instantiation,[status(thm)],[c_324]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_0,plain,
% 0.81/0.93      ( r2_relset_1(X0,X1,X2,X2)
% 0.81/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.81/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.81/0.93      inference(cnf_transformation,[],[f17]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_4,negated_conjecture,
% 0.81/0.93      ( ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
% 0.81/0.93      inference(cnf_transformation,[],[f28]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_127,plain,
% 0.81/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.81/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.81/0.93      | sK2 != X3
% 0.81/0.93      | sK1 != X3
% 0.81/0.93      | sK0 != X2
% 0.81/0.93      | sK0 != X1 ),
% 0.81/0.93      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_128,plain,
% 0.81/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.81/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.81/0.93      | sK1 != sK2 ),
% 0.81/0.93      inference(unflattening,[status(thm)],[c_127]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_132,plain,
% 0.81/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 != sK2 ),
% 0.81/0.93      inference(global_propositional_subsumption,[status(thm)],[c_128,c_6]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_320,plain,
% 0.81/0.93      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 != sK2 ),
% 0.81/0.93      inference(subtyping,[status(esa)],[c_132]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_346,plain,
% 0.81/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 != sK2 ),
% 0.81/0.93      inference(instantiation,[status(thm)],[c_320]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_348,plain,
% 0.81/0.93      ( sK2 = sK1
% 0.81/0.93      | v1_partfun1(sK2,X0_41) != iProver_top
% 0.81/0.93      | v1_partfun1(sK1,X0_41) != iProver_top
% 0.81/0.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top
% 0.81/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top ),
% 0.81/0.93      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_328,plain,
% 0.81/0.93      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 0.81/0.93      theory(equality) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_555,plain,
% 0.81/0.93      ( sK2 != X0_40 | sK1 != X0_40 | sK1 = sK2 ),
% 0.81/0.93      inference(instantiation,[status(thm)],[c_328]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_556,plain,
% 0.81/0.93      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 0.81/0.93      inference(instantiation,[status(thm)],[c_555]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_606,plain,
% 0.81/0.93      ( v1_partfun1(sK2,X0_41) != iProver_top
% 0.81/0.93      | v1_partfun1(sK1,X0_41) != iProver_top
% 0.81/0.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top
% 0.81/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0_41,X1_41))) != iProver_top ),
% 0.81/0.93      inference(global_propositional_subsumption,
% 0.81/0.93                [status(thm)],
% 0.81/0.93                [c_483,c_9,c_339,c_346,c_348,c_556]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_616,plain,
% 0.81/0.93      ( v1_partfun1(sK2,sK0) != iProver_top
% 0.81/0.93      | v1_partfun1(sK1,sK0) != iProver_top
% 0.81/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 0.81/0.93      inference(superposition,[status(thm)],[c_480,c_606]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_617,plain,
% 0.81/0.93      ( ~ v1_partfun1(sK2,sK0)
% 0.81/0.93      | ~ v1_partfun1(sK1,sK0)
% 0.81/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 0.81/0.93      inference(predicate_to_equality_rev,[status(thm)],[c_616]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_674,plain,
% 0.81/0.93      ( k1_xboole_0 = sK0 ),
% 0.81/0.93      inference(global_propositional_subsumption,
% 0.81/0.93                [status(thm)],
% 0.81/0.93                [c_486,c_9,c_6,c_339,c_346,c_349,c_316,c_315,c_556]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_14,plain,
% 0.81/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 0.81/0.93      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_667,plain,
% 0.81/0.93      ( v1_partfun1(sK1,sK0) != iProver_top
% 0.81/0.93      | v1_partfun1(sK2,sK0) != iProver_top ),
% 0.81/0.93      inference(global_propositional_subsumption,[status(thm)],[c_616,c_14]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_668,plain,
% 0.81/0.93      ( v1_partfun1(sK2,sK0) != iProver_top
% 0.81/0.93      | v1_partfun1(sK1,sK0) != iProver_top ),
% 0.81/0.93      inference(renaming,[status(thm)],[c_667]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_677,plain,
% 0.81/0.93      ( v1_partfun1(sK2,k1_xboole_0) != iProver_top
% 0.81/0.93      | v1_partfun1(sK1,k1_xboole_0) != iProver_top ),
% 0.81/0.93      inference(demodulation,[status(thm)],[c_674,c_668]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_1,plain,
% 0.81/0.93      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 0.81/0.93      | v1_partfun1(X0,k1_xboole_0)
% 0.81/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.81/0.93      | ~ v1_funct_1(X0) ),
% 0.81/0.93      inference(cnf_transformation,[],[f29]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_198,plain,
% 0.81/0.93      ( v1_partfun1(X0,k1_xboole_0)
% 0.81/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.81/0.93      | ~ v1_funct_1(X0)
% 0.81/0.93      | sK1 != X0
% 0.81/0.93      | sK0 != X1
% 0.81/0.93      | sK0 != k1_xboole_0 ),
% 0.81/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_10]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_199,plain,
% 0.81/0.93      ( v1_partfun1(sK1,k1_xboole_0)
% 0.81/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.81/0.93      | ~ v1_funct_1(sK1)
% 0.81/0.93      | sK0 != k1_xboole_0 ),
% 0.81/0.93      inference(unflattening,[status(thm)],[c_198]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_201,plain,
% 0.81/0.93      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.81/0.93      | v1_partfun1(sK1,k1_xboole_0)
% 0.81/0.93      | sK0 != k1_xboole_0 ),
% 0.81/0.93      inference(global_propositional_subsumption,[status(thm)],[c_199,c_11]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_202,plain,
% 0.81/0.93      ( v1_partfun1(sK1,k1_xboole_0)
% 0.81/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.81/0.93      | sK0 != k1_xboole_0 ),
% 0.81/0.93      inference(renaming,[status(thm)],[c_201]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_317,plain,
% 0.81/0.93      ( v1_partfun1(sK1,k1_xboole_0)
% 0.81/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.81/0.93      | sK0 != k1_xboole_0 ),
% 0.81/0.93      inference(subtyping,[status(esa)],[c_202]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_485,plain,
% 0.81/0.93      ( sK0 != k1_xboole_0
% 0.81/0.93      | v1_partfun1(sK1,k1_xboole_0) = iProver_top
% 0.81/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.81/0.93      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_325,plain,( X0_41 = X0_41 ),theory(equality) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_340,plain,
% 0.81/0.93      ( sK0 = sK0 ),
% 0.81/0.93      inference(instantiation,[status(thm)],[c_325]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_349,plain,
% 0.81/0.93      ( ~ v1_partfun1(sK2,sK0)
% 0.81/0.93      | ~ v1_partfun1(sK1,sK0)
% 0.81/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.81/0.93      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 0.81/0.93      | sK2 = sK1 ),
% 0.81/0.93      inference(instantiation,[status(thm)],[c_319]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_352,plain,
% 0.81/0.93      ( sK0 != k1_xboole_0
% 0.81/0.93      | v1_partfun1(sK1,k1_xboole_0) = iProver_top
% 0.81/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.81/0.93      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_329,plain,
% 0.81/0.93      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 0.81/0.93      theory(equality) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_557,plain,
% 0.81/0.93      ( sK0 != X0_41 | sK0 = k1_xboole_0 | k1_xboole_0 != X0_41 ),
% 0.81/0.93      inference(instantiation,[status(thm)],[c_329]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_558,plain,
% 0.81/0.93      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 0.81/0.93      inference(instantiation,[status(thm)],[c_557]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_599,plain,
% 0.81/0.93      ( v1_partfun1(sK1,k1_xboole_0) = iProver_top
% 0.81/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.81/0.93      inference(global_propositional_subsumption,
% 0.81/0.93                [status(thm)],
% 0.81/0.93                [c_485,c_9,c_6,c_339,c_340,c_346,c_349,c_352,c_316,c_315,
% 0.81/0.93                 c_556,c_558]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_678,plain,
% 0.81/0.93      ( v1_partfun1(sK1,k1_xboole_0) = iProver_top
% 0.81/0.93      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 0.81/0.93      inference(demodulation,[status(thm)],[c_674,c_599]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_321,negated_conjecture,
% 0.81/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 0.81/0.93      inference(subtyping,[status(esa)],[c_9]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_481,plain,
% 0.81/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 0.81/0.93      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_680,plain,
% 0.81/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 0.81/0.93      inference(demodulation,[status(thm)],[c_674,c_481]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_692,plain,
% 0.81/0.93      ( v1_partfun1(sK1,k1_xboole_0) = iProver_top ),
% 0.81/0.93      inference(forward_subsumption_resolution,[status(thm)],[c_678,c_680]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_181,plain,
% 0.81/0.93      ( v1_partfun1(X0,k1_xboole_0)
% 0.81/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.81/0.93      | ~ v1_funct_1(X0)
% 0.81/0.93      | sK2 != X0
% 0.81/0.93      | sK0 != X1
% 0.81/0.93      | sK0 != k1_xboole_0 ),
% 0.81/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_182,plain,
% 0.81/0.93      ( v1_partfun1(sK2,k1_xboole_0)
% 0.81/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.81/0.93      | ~ v1_funct_1(sK2)
% 0.81/0.93      | sK0 != k1_xboole_0 ),
% 0.81/0.93      inference(unflattening,[status(thm)],[c_181]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_184,plain,
% 0.81/0.93      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.81/0.93      | v1_partfun1(sK2,k1_xboole_0)
% 0.81/0.93      | sK0 != k1_xboole_0 ),
% 0.81/0.93      inference(global_propositional_subsumption,[status(thm)],[c_182,c_8]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_185,plain,
% 0.81/0.93      ( v1_partfun1(sK2,k1_xboole_0)
% 0.81/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.81/0.93      | sK0 != k1_xboole_0 ),
% 0.81/0.93      inference(renaming,[status(thm)],[c_184]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_318,plain,
% 0.81/0.93      ( v1_partfun1(sK2,k1_xboole_0)
% 0.81/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 0.81/0.93      | sK0 != k1_xboole_0 ),
% 0.81/0.93      inference(subtyping,[status(esa)],[c_185]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_484,plain,
% 0.81/0.93      ( sK0 != k1_xboole_0
% 0.81/0.93      | v1_partfun1(sK2,k1_xboole_0) = iProver_top
% 0.81/0.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.81/0.93      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_351,plain,
% 0.81/0.93      ( sK0 != k1_xboole_0
% 0.81/0.93      | v1_partfun1(sK2,k1_xboole_0) = iProver_top
% 0.81/0.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.81/0.93      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_571,plain,
% 0.81/0.93      ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
% 0.81/0.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.81/0.93      inference(global_propositional_subsumption,
% 0.81/0.93                [status(thm)],
% 0.81/0.93                [c_484,c_9,c_6,c_339,c_340,c_346,c_349,c_351,c_316,c_315,
% 0.81/0.93                 c_556,c_558]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_679,plain,
% 0.81/0.93      ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
% 0.81/0.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 0.81/0.93      inference(demodulation,[status(thm)],[c_674,c_571]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_681,plain,
% 0.81/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 0.81/0.93      inference(demodulation,[status(thm)],[c_674,c_480]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_688,plain,
% 0.81/0.93      ( v1_partfun1(sK2,k1_xboole_0) = iProver_top ),
% 0.81/0.93      inference(forward_subsumption_resolution,[status(thm)],[c_679,c_681]) ).
% 0.81/0.93  
% 0.81/0.93  cnf(c_696,plain,
% 0.81/0.93      ( $false ),
% 0.81/0.93      inference(forward_subsumption_resolution,
% 0.81/0.93                [status(thm)],
% 0.81/0.93                [c_677,c_692,c_688]) ).
% 0.81/0.93  
% 0.81/0.93  
% 0.81/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 0.81/0.93  
% 0.81/0.93  ------                               Statistics
% 0.81/0.93  
% 0.81/0.93  ------ General
% 0.81/0.93  
% 0.81/0.93  abstr_ref_over_cycles:                  0
% 0.81/0.93  abstr_ref_under_cycles:                 0
% 0.81/0.93  gc_basic_clause_elim:                   0
% 0.81/0.93  forced_gc_time:                         0
% 0.81/0.93  parsing_time:                           0.009
% 0.81/0.93  unif_index_cands_time:                  0.
% 0.81/0.93  unif_index_add_time:                    0.
% 0.81/0.93  orderings_time:                         0.
% 0.81/0.93  out_proof_time:                         0.012
% 0.81/0.93  total_time:                             0.059
% 0.81/0.93  num_of_symbols:                         44
% 0.81/0.93  num_of_terms:                           669
% 0.81/0.93  
% 0.81/0.93  ------ Preprocessing
% 0.81/0.93  
% 0.81/0.93  num_of_splits:                          0
% 0.81/0.93  num_of_split_atoms:                     0
% 0.81/0.93  num_of_reused_defs:                     0
% 0.81/0.93  num_eq_ax_congr_red:                    1
% 0.81/0.93  num_of_sem_filtered_clauses:            1
% 0.81/0.93  num_of_subtypes:                        4
% 0.81/0.93  monotx_restored_types:                  0
% 0.81/0.93  sat_num_of_epr_types:                   0
% 0.81/0.93  sat_num_of_non_cyclic_types:            0
% 0.81/0.93  sat_guarded_non_collapsed_types:        0
% 0.81/0.93  num_pure_diseq_elim:                    0
% 0.81/0.93  simp_replaced_by:                       0
% 0.81/0.93  res_preprocessed:                       57
% 0.81/0.93  prep_upred:                             0
% 0.81/0.93  prep_unflattend:                        15
% 0.81/0.93  smt_new_axioms:                         0
% 0.81/0.93  pred_elim_cands:                        2
% 0.81/0.93  pred_elim:                              4
% 0.81/0.93  pred_elim_cl:                           4
% 0.81/0.93  pred_elim_cycles:                       6
% 0.81/0.93  merged_defs:                            0
% 0.81/0.93  merged_defs_ncl:                        0
% 0.81/0.93  bin_hyper_res:                          0
% 0.81/0.93  prep_cycles:                            4
% 0.81/0.93  pred_elim_time:                         0.003
% 0.81/0.93  splitting_time:                         0.
% 0.81/0.93  sem_filter_time:                        0.
% 0.81/0.93  monotx_time:                            0.
% 0.81/0.93  subtype_inf_time:                       0.
% 0.81/0.93  
% 0.81/0.93  ------ Problem properties
% 0.81/0.93  
% 0.81/0.93  clauses:                                8
% 0.81/0.93  conjectures:                            2
% 0.81/0.93  epr:                                    2
% 0.81/0.93  horn:                                   6
% 0.81/0.93  ground:                                 6
% 0.81/0.93  unary:                                  2
% 0.81/0.93  binary:                                 3
% 0.81/0.93  lits:                                   19
% 0.81/0.93  lits_eq:                                6
% 0.81/0.93  fd_pure:                                0
% 0.81/0.93  fd_pseudo:                              0
% 0.81/0.93  fd_cond:                                0
% 0.81/0.93  fd_pseudo_cond:                         0
% 0.81/0.93  ac_symbols:                             0
% 0.81/0.93  
% 0.81/0.93  ------ Propositional Solver
% 0.81/0.93  
% 0.81/0.93  prop_solver_calls:                      24
% 0.81/0.93  prop_fast_solver_calls:                 337
% 0.81/0.93  smt_solver_calls:                       0
% 0.81/0.93  smt_fast_solver_calls:                  0
% 0.81/0.93  prop_num_of_clauses:                    163
% 0.81/0.93  prop_preprocess_simplified:             1163
% 0.81/0.93  prop_fo_subsumed:                       16
% 0.81/0.93  prop_solver_time:                       0.
% 0.81/0.93  smt_solver_time:                        0.
% 0.81/0.93  smt_fast_solver_time:                   0.
% 0.81/0.93  prop_fast_solver_time:                  0.
% 0.81/0.93  prop_unsat_core_time:                   0.
% 0.81/0.93  
% 0.81/0.93  ------ QBF
% 0.81/0.93  
% 0.81/0.93  qbf_q_res:                              0
% 0.81/0.93  qbf_num_tautologies:                    0
% 0.81/0.93  qbf_prep_cycles:                        0
% 0.81/0.93  
% 0.81/0.93  ------ BMC1
% 0.81/0.93  
% 0.81/0.93  bmc1_current_bound:                     -1
% 0.81/0.93  bmc1_last_solved_bound:                 -1
% 0.81/0.93  bmc1_unsat_core_size:                   -1
% 0.81/0.93  bmc1_unsat_core_parents_size:           -1
% 0.81/0.93  bmc1_merge_next_fun:                    0
% 0.81/0.93  bmc1_unsat_core_clauses_time:           0.
% 0.81/0.93  
% 0.81/0.93  ------ Instantiation
% 0.81/0.93  
% 0.81/0.93  inst_num_of_clauses:                    40
% 0.81/0.93  inst_num_in_passive:                    5
% 0.81/0.93  inst_num_in_active:                     33
% 0.81/0.93  inst_num_in_unprocessed:                2
% 0.81/0.93  inst_num_of_loops:                      40
% 0.81/0.93  inst_num_of_learning_restarts:          0
% 0.81/0.93  inst_num_moves_active_passive:          5
% 0.81/0.93  inst_lit_activity:                      0
% 0.81/0.93  inst_lit_activity_moves:                0
% 0.81/0.93  inst_num_tautologies:                   0
% 0.81/0.93  inst_num_prop_implied:                  0
% 0.81/0.93  inst_num_existing_simplified:           0
% 0.81/0.93  inst_num_eq_res_simplified:             0
% 0.81/0.93  inst_num_child_elim:                    0
% 0.81/0.93  inst_num_of_dismatching_blockings:      2
% 0.81/0.93  inst_num_of_non_proper_insts:           22
% 0.81/0.93  inst_num_of_duplicates:                 0
% 0.81/0.93  inst_inst_num_from_inst_to_res:         0
% 0.81/0.93  inst_dismatching_checking_time:         0.
% 0.81/0.93  
% 0.81/0.93  ------ Resolution
% 0.81/0.93  
% 0.81/0.93  res_num_of_clauses:                     0
% 0.81/0.93  res_num_in_passive:                     0
% 0.81/0.93  res_num_in_active:                      0
% 0.81/0.93  res_num_of_loops:                       61
% 0.81/0.93  res_forward_subset_subsumed:            5
% 0.81/0.93  res_backward_subset_subsumed:           0
% 0.81/0.93  res_forward_subsumed:                   0
% 0.81/0.93  res_backward_subsumed:                  0
% 0.81/0.93  res_forward_subsumption_resolution:     0
% 0.81/0.93  res_backward_subsumption_resolution:    0
% 0.81/0.93  res_clause_to_clause_subsumption:       16
% 0.81/0.93  res_orphan_elimination:                 0
% 0.81/0.93  res_tautology_del:                      2
% 0.81/0.93  res_num_eq_res_simplified:              0
% 0.81/0.93  res_num_sel_changes:                    0
% 0.81/0.93  res_moves_from_active_to_pass:          0
% 0.81/0.93  
% 0.81/0.93  ------ Superposition
% 0.81/0.93  
% 0.81/0.93  sup_time_total:                         0.
% 0.81/0.93  sup_time_generating:                    0.
% 0.81/0.93  sup_time_sim_full:                      0.
% 0.81/0.93  sup_time_sim_immed:                     0.
% 0.81/0.93  
% 0.81/0.93  sup_num_of_clauses:                     3
% 0.81/0.93  sup_num_in_active:                      2
% 0.81/0.93  sup_num_in_passive:                     1
% 0.81/0.93  sup_num_of_loops:                       7
% 0.81/0.93  sup_fw_superposition:                   1
% 0.81/0.93  sup_bw_superposition:                   0
% 0.81/0.93  sup_immediate_simplified:               0
% 0.81/0.93  sup_given_eliminated:                   0
% 0.81/0.93  comparisons_done:                       0
% 0.81/0.93  comparisons_avoided:                    0
% 0.81/0.93  
% 0.81/0.93  ------ Simplifications
% 0.81/0.93  
% 0.81/0.93  
% 0.81/0.93  sim_fw_subset_subsumed:                 0
% 0.81/0.93  sim_bw_subset_subsumed:                 1
% 0.81/0.93  sim_fw_subsumed:                        0
% 0.81/0.93  sim_bw_subsumed:                        0
% 0.81/0.93  sim_fw_subsumption_res:                 4
% 0.81/0.93  sim_bw_subsumption_res:                 0
% 0.81/0.93  sim_tautology_del:                      0
% 0.81/0.93  sim_eq_tautology_del:                   0
% 0.81/0.93  sim_eq_res_simp:                        0
% 0.81/0.93  sim_fw_demodulated:                     0
% 0.81/0.93  sim_bw_demodulated:                     5
% 0.81/0.93  sim_light_normalised:                   0
% 0.81/0.93  sim_joinable_taut:                      0
% 0.81/0.93  sim_joinable_simp:                      0
% 0.81/0.93  sim_ac_normalised:                      0
% 0.81/0.93  sim_smt_subsumption:                    0
% 0.81/0.93  
%------------------------------------------------------------------------------
