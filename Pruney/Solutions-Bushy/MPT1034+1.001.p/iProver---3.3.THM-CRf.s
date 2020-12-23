%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1034+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:43 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 504 expanded)
%              Number of clauses        :   35 (  95 expanded)
%              Number of leaves         :    4 ( 150 expanded)
%              Depth                    :   15
%              Number of atoms          :  238 (3730 expanded)
%              Number of equality atoms :   47 ( 117 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f4])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_xboole_0 != X0
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X2,X3,X1] :
      ( r2_relset_1(k1_xboole_0,X1,X2,X3)
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f12])).

fof(f2,conjecture,(
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

fof(f3,negated_conjecture,(
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
    inference(negated_conjecture,[],[f2])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f9,plain,(
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

fof(f8,plain,
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

fof(f10,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    & r1_partfun1(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9,f8])).

fof(f20,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f14,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_0,plain,
    ( r2_relset_1(k1_xboole_0,X0,X1,X2)
    | ~ v1_funct_2(X2,k1_xboole_0,X0)
    | ~ v1_funct_2(X1,k1_xboole_0,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ r1_partfun1(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_2,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_104,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_partfun1(X2,X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_105,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,sK0)
    | ~ v1_funct_2(sK1,k1_xboole_0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_104])).

cnf(c_9,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_6,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,negated_conjecture,
    ( r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_107,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(sK1,k1_xboole_0,sK0)
    | ~ v1_funct_2(sK2,k1_xboole_0,sK0)
    | sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_105,c_9,c_6,c_3])).

cnf(c_108,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,sK0)
    | ~ v1_funct_2(sK1,k1_xboole_0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_107])).

cnf(c_180,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,sK0)
    | ~ v1_funct_2(sK1,k1_xboole_0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_108])).

cnf(c_302,plain,
    ( sK0 != k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,sK0) != iProver_top
    | v1_funct_2(sK1,k1_xboole_0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_1,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_partfun1(X2,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_127,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_partfun1(X3,X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X3
    | sK0 != X1
    | sK0 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_128,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_127])).

cnf(c_8,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_5,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_130,plain,
    ( k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_128,c_9,c_8,c_7,c_6,c_5,c_4,c_3])).

cnf(c_179,plain,
    ( k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_130])).

cnf(c_317,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_302,c_179])).

cnf(c_318,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_317])).

cnf(c_182,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_300,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_182])).

cnf(c_314,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_300,c_179])).

cnf(c_184,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_298,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_311,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_298,c_179])).

cnf(c_181,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_301,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_181])).

cnf(c_308,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_301,c_179])).

cnf(c_183,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_299,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_305,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_299,c_179])).

cnf(c_323,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_318,c_314,c_311,c_308,c_305])).


%------------------------------------------------------------------------------
