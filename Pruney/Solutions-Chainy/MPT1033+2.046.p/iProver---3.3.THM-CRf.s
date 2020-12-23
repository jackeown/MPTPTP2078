%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:37 EST 2020

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  112 (2779 expanded)
%              Number of clauses        :   82 ( 747 expanded)
%              Number of leaves         :   10 ( 759 expanded)
%              Depth                    :   18
%              Number of atoms          :  417 (22737 expanded)
%              Number of equality atoms :  160 (5143 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
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

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK3)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_partfun1(X2,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3,X0,X1)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f15,f14])).

fof(f25,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
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
    r1_partfun1(sK2,sK3) ),
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

fof(f29,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
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

fof(f30,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f19])).

fof(f28,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_8,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_216,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_217,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_9,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_219,plain,
    ( v1_partfun1(sK3,sK0)
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_217,c_9,c_7])).

cnf(c_317,plain,
    ( v1_partfun1(sK3,sK0)
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_219])).

cnf(c_488,plain,
    ( k1_xboole_0 = sK1
    | v1_partfun1(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_230,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_231,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_233,plain,
    ( v1_partfun1(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_231,c_12,c_10])).

cnf(c_316,plain,
    ( v1_partfun1(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(subtyping,[status(esa)],[c_233])).

cnf(c_323,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_482,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

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

cnf(c_6,negated_conjecture,
    ( r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_149,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_partfun1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | X0 = X2
    | sK3 != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_150,plain,
    ( ~ v1_partfun1(sK3,X0)
    | ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_149])).

cnf(c_154,plain,
    ( ~ v1_partfun1(sK3,X0)
    | ~ v1_partfun1(sK2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_150,c_12,c_9])).

cnf(c_320,plain,
    ( ~ v1_partfun1(sK3,X0_42)
    | ~ v1_partfun1(sK2,X0_42)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42)))
    | sK3 = sK2 ),
    inference(subtyping,[status(esa)],[c_154])).

cnf(c_485,plain,
    ( sK3 = sK2
    | v1_partfun1(sK3,X0_42) != iProver_top
    | v1_partfun1(sK2,X0_42) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_326,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_341,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_0,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK3 != X3
    | sK2 != X3
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_129,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK2 != sK3 ),
    inference(unflattening,[status(thm)],[c_128])).

cnf(c_133,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK2 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_129,c_7])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK2 != sK3 ),
    inference(subtyping,[status(esa)],[c_133])).

cnf(c_348,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK2 != sK3 ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_350,plain,
    ( sK3 = sK2
    | v1_partfun1(sK3,X0_42) != iProver_top
    | v1_partfun1(sK2,X0_42) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_330,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_558,plain,
    ( sK3 != X0_41
    | sK2 != X0_41
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_559,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_672,plain,
    ( v1_partfun1(sK3,X0_42) != iProver_top
    | v1_partfun1(sK2,X0_42) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_10,c_341,c_348,c_350,c_559])).

cnf(c_682,plain,
    ( v1_partfun1(sK3,sK0) != iProver_top
    | v1_partfun1(sK2,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_482,c_672])).

cnf(c_683,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_682])).

cnf(c_710,plain,
    ( k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_10,c_7,c_341,c_348,c_317,c_316,c_559,c_605])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_199,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | sK2 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_200,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(sK2)
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_202,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | v1_partfun1(sK2,k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_200,c_12])).

cnf(c_203,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_318,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_203])).

cnf(c_487,plain,
    ( sK0 != k1_xboole_0
    | v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_5,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_324,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_354,plain,
    ( sK0 != k1_xboole_0
    | v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_549,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_42)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_42)))
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_320])).

cnf(c_605,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_331,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_560,plain,
    ( sK0 != X0_42
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0_42 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_610,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_327,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_611,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_628,plain,
    ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_10,c_7,c_341,c_324,c_348,c_354,c_317,c_316,c_559,c_605,c_610,c_611])).

cnf(c_713,plain,
    ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_710,c_628])).

cnf(c_322,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_483,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_715,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_710,c_483])).

cnf(c_717,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_710,c_324])).

cnf(c_718,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_717])).

cnf(c_724,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_715,c_718])).

cnf(c_733,plain,
    ( v1_partfun1(sK2,k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_713,c_724])).

cnf(c_182,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_183,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_185,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | v1_partfun1(sK3,k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_183,c_9])).

cnf(c_186,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_319,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | sK0 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_186])).

cnf(c_486,plain,
    ( sK0 != k1_xboole_0
    | v1_partfun1(sK3,k1_xboole_0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_353,plain,
    ( sK0 != k1_xboole_0
    | v1_partfun1(sK3,k1_xboole_0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_621,plain,
    ( v1_partfun1(sK3,k1_xboole_0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_10,c_7,c_341,c_324,c_348,c_353,c_317,c_316,c_559,c_605,c_610,c_611])).

cnf(c_714,plain,
    ( v1_partfun1(sK3,k1_xboole_0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_710,c_621])).

cnf(c_716,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_710,c_482])).

cnf(c_721,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_716,c_718])).

cnf(c_729,plain,
    ( v1_partfun1(sK3,k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_714,c_721])).

cnf(c_352,plain,
    ( sK3 = sK2
    | v1_partfun1(sK3,k1_xboole_0) != iProver_top
    | v1_partfun1(sK2,k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_733,c_729,c_724,c_721,c_559,c_352,c_348,c_341,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.86/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.86/1.00  
% 0.86/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.86/1.00  
% 0.86/1.00  ------  iProver source info
% 0.86/1.00  
% 0.86/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.86/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.86/1.00  git: non_committed_changes: false
% 0.86/1.00  git: last_make_outside_of_git: false
% 0.86/1.00  
% 0.86/1.00  ------ 
% 0.86/1.00  
% 0.86/1.00  ------ Input Options
% 0.86/1.00  
% 0.86/1.00  --out_options                           all
% 0.86/1.00  --tptp_safe_out                         true
% 0.86/1.00  --problem_path                          ""
% 0.86/1.00  --include_path                          ""
% 0.86/1.00  --clausifier                            res/vclausify_rel
% 0.86/1.00  --clausifier_options                    --mode clausify
% 0.86/1.00  --stdin                                 false
% 0.86/1.00  --stats_out                             all
% 0.86/1.00  
% 0.86/1.00  ------ General Options
% 0.86/1.00  
% 0.86/1.00  --fof                                   false
% 0.86/1.00  --time_out_real                         305.
% 0.86/1.00  --time_out_virtual                      -1.
% 0.86/1.00  --symbol_type_check                     false
% 0.86/1.00  --clausify_out                          false
% 0.86/1.00  --sig_cnt_out                           false
% 0.86/1.00  --trig_cnt_out                          false
% 0.86/1.00  --trig_cnt_out_tolerance                1.
% 0.86/1.00  --trig_cnt_out_sk_spl                   false
% 0.86/1.00  --abstr_cl_out                          false
% 0.86/1.00  
% 0.86/1.00  ------ Global Options
% 0.86/1.00  
% 0.86/1.00  --schedule                              default
% 0.86/1.00  --add_important_lit                     false
% 0.86/1.00  --prop_solver_per_cl                    1000
% 0.86/1.00  --min_unsat_core                        false
% 0.86/1.00  --soft_assumptions                      false
% 0.86/1.00  --soft_lemma_size                       3
% 0.86/1.00  --prop_impl_unit_size                   0
% 0.86/1.00  --prop_impl_unit                        []
% 0.86/1.00  --share_sel_clauses                     true
% 0.86/1.00  --reset_solvers                         false
% 0.86/1.00  --bc_imp_inh                            [conj_cone]
% 0.86/1.00  --conj_cone_tolerance                   3.
% 0.86/1.00  --extra_neg_conj                        none
% 0.86/1.00  --large_theory_mode                     true
% 0.86/1.00  --prolific_symb_bound                   200
% 0.86/1.00  --lt_threshold                          2000
% 0.86/1.00  --clause_weak_htbl                      true
% 0.86/1.00  --gc_record_bc_elim                     false
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing Options
% 0.86/1.00  
% 0.86/1.00  --preprocessing_flag                    true
% 0.86/1.00  --time_out_prep_mult                    0.1
% 0.86/1.00  --splitting_mode                        input
% 0.86/1.00  --splitting_grd                         true
% 0.86/1.00  --splitting_cvd                         false
% 0.86/1.00  --splitting_cvd_svl                     false
% 0.86/1.00  --splitting_nvd                         32
% 0.86/1.00  --sub_typing                            true
% 0.86/1.00  --prep_gs_sim                           true
% 0.86/1.00  --prep_unflatten                        true
% 0.86/1.00  --prep_res_sim                          true
% 0.86/1.00  --prep_upred                            true
% 0.86/1.00  --prep_sem_filter                       exhaustive
% 0.86/1.00  --prep_sem_filter_out                   false
% 0.86/1.00  --pred_elim                             true
% 0.86/1.00  --res_sim_input                         true
% 0.86/1.00  --eq_ax_congr_red                       true
% 0.86/1.00  --pure_diseq_elim                       true
% 0.86/1.00  --brand_transform                       false
% 0.86/1.00  --non_eq_to_eq                          false
% 0.86/1.00  --prep_def_merge                        true
% 0.86/1.00  --prep_def_merge_prop_impl              false
% 0.86/1.00  --prep_def_merge_mbd                    true
% 0.86/1.00  --prep_def_merge_tr_red                 false
% 0.86/1.00  --prep_def_merge_tr_cl                  false
% 0.86/1.00  --smt_preprocessing                     true
% 0.86/1.00  --smt_ac_axioms                         fast
% 0.86/1.00  --preprocessed_out                      false
% 0.86/1.00  --preprocessed_stats                    false
% 0.86/1.00  
% 0.86/1.00  ------ Abstraction refinement Options
% 0.86/1.00  
% 0.86/1.00  --abstr_ref                             []
% 0.86/1.00  --abstr_ref_prep                        false
% 0.86/1.00  --abstr_ref_until_sat                   false
% 0.86/1.00  --abstr_ref_sig_restrict                funpre
% 0.86/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.86/1.00  --abstr_ref_under                       []
% 0.86/1.00  
% 0.86/1.00  ------ SAT Options
% 0.86/1.00  
% 0.86/1.00  --sat_mode                              false
% 0.86/1.00  --sat_fm_restart_options                ""
% 0.86/1.00  --sat_gr_def                            false
% 0.86/1.00  --sat_epr_types                         true
% 0.86/1.00  --sat_non_cyclic_types                  false
% 0.86/1.00  --sat_finite_models                     false
% 0.86/1.00  --sat_fm_lemmas                         false
% 0.86/1.00  --sat_fm_prep                           false
% 0.86/1.00  --sat_fm_uc_incr                        true
% 0.86/1.00  --sat_out_model                         small
% 0.86/1.00  --sat_out_clauses                       false
% 0.86/1.00  
% 0.86/1.00  ------ QBF Options
% 0.86/1.00  
% 0.86/1.00  --qbf_mode                              false
% 0.86/1.00  --qbf_elim_univ                         false
% 0.86/1.00  --qbf_dom_inst                          none
% 0.86/1.00  --qbf_dom_pre_inst                      false
% 0.86/1.00  --qbf_sk_in                             false
% 0.86/1.00  --qbf_pred_elim                         true
% 0.86/1.00  --qbf_split                             512
% 0.86/1.00  
% 0.86/1.00  ------ BMC1 Options
% 0.86/1.00  
% 0.86/1.00  --bmc1_incremental                      false
% 0.86/1.00  --bmc1_axioms                           reachable_all
% 0.86/1.00  --bmc1_min_bound                        0
% 0.86/1.00  --bmc1_max_bound                        -1
% 0.86/1.00  --bmc1_max_bound_default                -1
% 0.86/1.00  --bmc1_symbol_reachability              true
% 0.86/1.00  --bmc1_property_lemmas                  false
% 0.86/1.00  --bmc1_k_induction                      false
% 0.86/1.00  --bmc1_non_equiv_states                 false
% 0.86/1.00  --bmc1_deadlock                         false
% 0.86/1.00  --bmc1_ucm                              false
% 0.86/1.00  --bmc1_add_unsat_core                   none
% 0.86/1.00  --bmc1_unsat_core_children              false
% 0.86/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.86/1.00  --bmc1_out_stat                         full
% 0.86/1.00  --bmc1_ground_init                      false
% 0.86/1.00  --bmc1_pre_inst_next_state              false
% 0.86/1.00  --bmc1_pre_inst_state                   false
% 0.86/1.00  --bmc1_pre_inst_reach_state             false
% 0.86/1.00  --bmc1_out_unsat_core                   false
% 0.86/1.00  --bmc1_aig_witness_out                  false
% 0.86/1.00  --bmc1_verbose                          false
% 0.86/1.00  --bmc1_dump_clauses_tptp                false
% 0.86/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.86/1.00  --bmc1_dump_file                        -
% 0.86/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.86/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.86/1.00  --bmc1_ucm_extend_mode                  1
% 0.86/1.00  --bmc1_ucm_init_mode                    2
% 0.86/1.00  --bmc1_ucm_cone_mode                    none
% 0.86/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.86/1.00  --bmc1_ucm_relax_model                  4
% 0.86/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.86/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.86/1.00  --bmc1_ucm_layered_model                none
% 0.86/1.00  --bmc1_ucm_max_lemma_size               10
% 0.86/1.00  
% 0.86/1.00  ------ AIG Options
% 0.86/1.00  
% 0.86/1.00  --aig_mode                              false
% 0.86/1.00  
% 0.86/1.00  ------ Instantiation Options
% 0.86/1.00  
% 0.86/1.00  --instantiation_flag                    true
% 0.86/1.00  --inst_sos_flag                         false
% 0.86/1.00  --inst_sos_phase                        true
% 0.86/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.86/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.86/1.00  --inst_lit_sel_side                     num_symb
% 0.86/1.00  --inst_solver_per_active                1400
% 0.86/1.00  --inst_solver_calls_frac                1.
% 0.86/1.00  --inst_passive_queue_type               priority_queues
% 0.86/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.86/1.00  --inst_passive_queues_freq              [25;2]
% 0.86/1.00  --inst_dismatching                      true
% 0.86/1.00  --inst_eager_unprocessed_to_passive     true
% 0.86/1.00  --inst_prop_sim_given                   true
% 0.86/1.00  --inst_prop_sim_new                     false
% 0.86/1.00  --inst_subs_new                         false
% 0.86/1.00  --inst_eq_res_simp                      false
% 0.86/1.00  --inst_subs_given                       false
% 0.86/1.00  --inst_orphan_elimination               true
% 0.86/1.00  --inst_learning_loop_flag               true
% 0.86/1.00  --inst_learning_start                   3000
% 0.86/1.00  --inst_learning_factor                  2
% 0.86/1.00  --inst_start_prop_sim_after_learn       3
% 0.86/1.00  --inst_sel_renew                        solver
% 0.86/1.00  --inst_lit_activity_flag                true
% 0.86/1.00  --inst_restr_to_given                   false
% 0.86/1.00  --inst_activity_threshold               500
% 0.86/1.00  --inst_out_proof                        true
% 0.86/1.00  
% 0.86/1.00  ------ Resolution Options
% 0.86/1.00  
% 0.86/1.00  --resolution_flag                       true
% 0.86/1.00  --res_lit_sel                           adaptive
% 0.86/1.00  --res_lit_sel_side                      none
% 0.86/1.00  --res_ordering                          kbo
% 0.86/1.00  --res_to_prop_solver                    active
% 0.86/1.00  --res_prop_simpl_new                    false
% 0.86/1.00  --res_prop_simpl_given                  true
% 0.86/1.00  --res_passive_queue_type                priority_queues
% 0.86/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.86/1.00  --res_passive_queues_freq               [15;5]
% 0.86/1.00  --res_forward_subs                      full
% 0.86/1.00  --res_backward_subs                     full
% 0.86/1.00  --res_forward_subs_resolution           true
% 0.86/1.00  --res_backward_subs_resolution          true
% 0.86/1.00  --res_orphan_elimination                true
% 0.86/1.00  --res_time_limit                        2.
% 0.86/1.00  --res_out_proof                         true
% 0.86/1.00  
% 0.86/1.00  ------ Superposition Options
% 0.86/1.00  
% 0.86/1.00  --superposition_flag                    true
% 0.86/1.00  --sup_passive_queue_type                priority_queues
% 0.86/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.86/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.86/1.00  --demod_completeness_check              fast
% 0.86/1.00  --demod_use_ground                      true
% 0.86/1.00  --sup_to_prop_solver                    passive
% 0.86/1.00  --sup_prop_simpl_new                    true
% 0.86/1.00  --sup_prop_simpl_given                  true
% 0.86/1.00  --sup_fun_splitting                     false
% 0.86/1.00  --sup_smt_interval                      50000
% 0.86/1.00  
% 0.86/1.00  ------ Superposition Simplification Setup
% 0.86/1.00  
% 0.86/1.00  --sup_indices_passive                   []
% 0.86/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.86/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_full_bw                           [BwDemod]
% 0.86/1.00  --sup_immed_triv                        [TrivRules]
% 0.86/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.86/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_immed_bw_main                     []
% 0.86/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.86/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.00  
% 0.86/1.00  ------ Combination Options
% 0.86/1.00  
% 0.86/1.00  --comb_res_mult                         3
% 0.86/1.00  --comb_sup_mult                         2
% 0.86/1.00  --comb_inst_mult                        10
% 0.86/1.00  
% 0.86/1.00  ------ Debug Options
% 0.86/1.00  
% 0.86/1.00  --dbg_backtrace                         false
% 0.86/1.00  --dbg_dump_prop_clauses                 false
% 0.86/1.00  --dbg_dump_prop_clauses_file            -
% 0.86/1.00  --dbg_out_stat                          false
% 0.86/1.00  ------ Parsing...
% 0.86/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.86/1.00  ------ Proving...
% 0.86/1.00  ------ Problem Properties 
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  clauses                                 9
% 0.86/1.00  conjectures                             3
% 0.86/1.00  EPR                                     3
% 0.86/1.00  Horn                                    7
% 0.86/1.00  unary                                   2
% 0.86/1.00  binary                                  4
% 0.86/1.00  lits                                    21
% 0.86/1.00  lits eq                                 8
% 0.86/1.00  fd_pure                                 0
% 0.86/1.00  fd_pseudo                               0
% 0.86/1.00  fd_cond                                 0
% 0.86/1.00  fd_pseudo_cond                          0
% 0.86/1.00  AC symbols                              0
% 0.86/1.00  
% 0.86/1.00  ------ Schedule dynamic 5 is on 
% 0.86/1.00  
% 0.86/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  ------ 
% 0.86/1.00  Current options:
% 0.86/1.00  ------ 
% 0.86/1.00  
% 0.86/1.00  ------ Input Options
% 0.86/1.00  
% 0.86/1.00  --out_options                           all
% 0.86/1.00  --tptp_safe_out                         true
% 0.86/1.00  --problem_path                          ""
% 0.86/1.00  --include_path                          ""
% 0.86/1.00  --clausifier                            res/vclausify_rel
% 0.86/1.00  --clausifier_options                    --mode clausify
% 0.86/1.00  --stdin                                 false
% 0.86/1.00  --stats_out                             all
% 0.86/1.00  
% 0.86/1.00  ------ General Options
% 0.86/1.00  
% 0.86/1.00  --fof                                   false
% 0.86/1.00  --time_out_real                         305.
% 0.86/1.00  --time_out_virtual                      -1.
% 0.86/1.00  --symbol_type_check                     false
% 0.86/1.00  --clausify_out                          false
% 0.86/1.00  --sig_cnt_out                           false
% 0.86/1.00  --trig_cnt_out                          false
% 0.86/1.00  --trig_cnt_out_tolerance                1.
% 0.86/1.00  --trig_cnt_out_sk_spl                   false
% 0.86/1.00  --abstr_cl_out                          false
% 0.86/1.00  
% 0.86/1.00  ------ Global Options
% 0.86/1.00  
% 0.86/1.00  --schedule                              default
% 0.86/1.00  --add_important_lit                     false
% 0.86/1.00  --prop_solver_per_cl                    1000
% 0.86/1.00  --min_unsat_core                        false
% 0.86/1.00  --soft_assumptions                      false
% 0.86/1.00  --soft_lemma_size                       3
% 0.86/1.00  --prop_impl_unit_size                   0
% 0.86/1.00  --prop_impl_unit                        []
% 0.86/1.00  --share_sel_clauses                     true
% 0.86/1.00  --reset_solvers                         false
% 0.86/1.00  --bc_imp_inh                            [conj_cone]
% 0.86/1.00  --conj_cone_tolerance                   3.
% 0.86/1.00  --extra_neg_conj                        none
% 0.86/1.00  --large_theory_mode                     true
% 0.86/1.00  --prolific_symb_bound                   200
% 0.86/1.00  --lt_threshold                          2000
% 0.86/1.00  --clause_weak_htbl                      true
% 0.86/1.00  --gc_record_bc_elim                     false
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing Options
% 0.86/1.00  
% 0.86/1.00  --preprocessing_flag                    true
% 0.86/1.00  --time_out_prep_mult                    0.1
% 0.86/1.00  --splitting_mode                        input
% 0.86/1.00  --splitting_grd                         true
% 0.86/1.00  --splitting_cvd                         false
% 0.86/1.00  --splitting_cvd_svl                     false
% 0.86/1.00  --splitting_nvd                         32
% 0.86/1.00  --sub_typing                            true
% 0.86/1.00  --prep_gs_sim                           true
% 0.86/1.00  --prep_unflatten                        true
% 0.86/1.00  --prep_res_sim                          true
% 0.86/1.00  --prep_upred                            true
% 0.86/1.00  --prep_sem_filter                       exhaustive
% 0.86/1.00  --prep_sem_filter_out                   false
% 0.86/1.00  --pred_elim                             true
% 0.86/1.00  --res_sim_input                         true
% 0.86/1.00  --eq_ax_congr_red                       true
% 0.86/1.00  --pure_diseq_elim                       true
% 0.86/1.00  --brand_transform                       false
% 0.86/1.00  --non_eq_to_eq                          false
% 0.86/1.00  --prep_def_merge                        true
% 0.86/1.00  --prep_def_merge_prop_impl              false
% 0.86/1.00  --prep_def_merge_mbd                    true
% 0.86/1.00  --prep_def_merge_tr_red                 false
% 0.86/1.00  --prep_def_merge_tr_cl                  false
% 0.86/1.00  --smt_preprocessing                     true
% 0.86/1.00  --smt_ac_axioms                         fast
% 0.86/1.00  --preprocessed_out                      false
% 0.86/1.00  --preprocessed_stats                    false
% 0.86/1.00  
% 0.86/1.00  ------ Abstraction refinement Options
% 0.86/1.00  
% 0.86/1.00  --abstr_ref                             []
% 0.86/1.00  --abstr_ref_prep                        false
% 0.86/1.00  --abstr_ref_until_sat                   false
% 0.86/1.00  --abstr_ref_sig_restrict                funpre
% 0.86/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.86/1.00  --abstr_ref_under                       []
% 0.86/1.00  
% 0.86/1.00  ------ SAT Options
% 0.86/1.00  
% 0.86/1.00  --sat_mode                              false
% 0.86/1.00  --sat_fm_restart_options                ""
% 0.86/1.00  --sat_gr_def                            false
% 0.86/1.00  --sat_epr_types                         true
% 0.86/1.00  --sat_non_cyclic_types                  false
% 0.86/1.00  --sat_finite_models                     false
% 0.86/1.00  --sat_fm_lemmas                         false
% 0.86/1.00  --sat_fm_prep                           false
% 0.86/1.00  --sat_fm_uc_incr                        true
% 0.86/1.00  --sat_out_model                         small
% 0.86/1.00  --sat_out_clauses                       false
% 0.86/1.00  
% 0.86/1.00  ------ QBF Options
% 0.86/1.00  
% 0.86/1.00  --qbf_mode                              false
% 0.86/1.00  --qbf_elim_univ                         false
% 0.86/1.00  --qbf_dom_inst                          none
% 0.86/1.00  --qbf_dom_pre_inst                      false
% 0.86/1.00  --qbf_sk_in                             false
% 0.86/1.00  --qbf_pred_elim                         true
% 0.86/1.00  --qbf_split                             512
% 0.86/1.00  
% 0.86/1.00  ------ BMC1 Options
% 0.86/1.00  
% 0.86/1.00  --bmc1_incremental                      false
% 0.86/1.00  --bmc1_axioms                           reachable_all
% 0.86/1.00  --bmc1_min_bound                        0
% 0.86/1.00  --bmc1_max_bound                        -1
% 0.86/1.00  --bmc1_max_bound_default                -1
% 0.86/1.00  --bmc1_symbol_reachability              true
% 0.86/1.00  --bmc1_property_lemmas                  false
% 0.86/1.00  --bmc1_k_induction                      false
% 0.86/1.00  --bmc1_non_equiv_states                 false
% 0.86/1.00  --bmc1_deadlock                         false
% 0.86/1.00  --bmc1_ucm                              false
% 0.86/1.00  --bmc1_add_unsat_core                   none
% 0.86/1.00  --bmc1_unsat_core_children              false
% 0.86/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.86/1.00  --bmc1_out_stat                         full
% 0.86/1.00  --bmc1_ground_init                      false
% 0.86/1.00  --bmc1_pre_inst_next_state              false
% 0.86/1.00  --bmc1_pre_inst_state                   false
% 0.86/1.00  --bmc1_pre_inst_reach_state             false
% 0.86/1.00  --bmc1_out_unsat_core                   false
% 0.86/1.00  --bmc1_aig_witness_out                  false
% 0.86/1.00  --bmc1_verbose                          false
% 0.86/1.00  --bmc1_dump_clauses_tptp                false
% 0.86/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.86/1.00  --bmc1_dump_file                        -
% 0.86/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.86/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.86/1.00  --bmc1_ucm_extend_mode                  1
% 0.86/1.00  --bmc1_ucm_init_mode                    2
% 0.86/1.00  --bmc1_ucm_cone_mode                    none
% 0.86/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.86/1.00  --bmc1_ucm_relax_model                  4
% 0.86/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.86/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.86/1.00  --bmc1_ucm_layered_model                none
% 0.86/1.00  --bmc1_ucm_max_lemma_size               10
% 0.86/1.00  
% 0.86/1.00  ------ AIG Options
% 0.86/1.00  
% 0.86/1.00  --aig_mode                              false
% 0.86/1.00  
% 0.86/1.00  ------ Instantiation Options
% 0.86/1.00  
% 0.86/1.00  --instantiation_flag                    true
% 0.86/1.00  --inst_sos_flag                         false
% 0.86/1.00  --inst_sos_phase                        true
% 0.86/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.86/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.86/1.00  --inst_lit_sel_side                     none
% 0.86/1.00  --inst_solver_per_active                1400
% 0.86/1.00  --inst_solver_calls_frac                1.
% 0.86/1.00  --inst_passive_queue_type               priority_queues
% 0.86/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.86/1.00  --inst_passive_queues_freq              [25;2]
% 0.86/1.00  --inst_dismatching                      true
% 0.86/1.00  --inst_eager_unprocessed_to_passive     true
% 0.86/1.00  --inst_prop_sim_given                   true
% 0.86/1.00  --inst_prop_sim_new                     false
% 0.86/1.00  --inst_subs_new                         false
% 0.86/1.00  --inst_eq_res_simp                      false
% 0.86/1.00  --inst_subs_given                       false
% 0.86/1.00  --inst_orphan_elimination               true
% 0.86/1.00  --inst_learning_loop_flag               true
% 0.86/1.00  --inst_learning_start                   3000
% 0.86/1.00  --inst_learning_factor                  2
% 0.86/1.00  --inst_start_prop_sim_after_learn       3
% 0.86/1.00  --inst_sel_renew                        solver
% 0.86/1.00  --inst_lit_activity_flag                true
% 0.86/1.00  --inst_restr_to_given                   false
% 0.86/1.00  --inst_activity_threshold               500
% 0.86/1.00  --inst_out_proof                        true
% 0.86/1.00  
% 0.86/1.00  ------ Resolution Options
% 0.86/1.00  
% 0.86/1.00  --resolution_flag                       false
% 0.86/1.00  --res_lit_sel                           adaptive
% 0.86/1.00  --res_lit_sel_side                      none
% 0.86/1.00  --res_ordering                          kbo
% 0.86/1.00  --res_to_prop_solver                    active
% 0.86/1.00  --res_prop_simpl_new                    false
% 0.86/1.00  --res_prop_simpl_given                  true
% 0.86/1.00  --res_passive_queue_type                priority_queues
% 0.86/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.86/1.00  --res_passive_queues_freq               [15;5]
% 0.86/1.00  --res_forward_subs                      full
% 0.86/1.00  --res_backward_subs                     full
% 0.86/1.00  --res_forward_subs_resolution           true
% 0.86/1.00  --res_backward_subs_resolution          true
% 0.86/1.00  --res_orphan_elimination                true
% 0.86/1.00  --res_time_limit                        2.
% 0.86/1.00  --res_out_proof                         true
% 0.86/1.00  
% 0.86/1.00  ------ Superposition Options
% 0.86/1.00  
% 0.86/1.00  --superposition_flag                    true
% 0.86/1.00  --sup_passive_queue_type                priority_queues
% 0.86/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.86/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.86/1.00  --demod_completeness_check              fast
% 0.86/1.00  --demod_use_ground                      true
% 0.86/1.00  --sup_to_prop_solver                    passive
% 0.86/1.00  --sup_prop_simpl_new                    true
% 0.86/1.00  --sup_prop_simpl_given                  true
% 0.86/1.00  --sup_fun_splitting                     false
% 0.86/1.00  --sup_smt_interval                      50000
% 0.86/1.00  
% 0.86/1.00  ------ Superposition Simplification Setup
% 0.86/1.00  
% 0.86/1.00  --sup_indices_passive                   []
% 0.86/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.86/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.86/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_full_bw                           [BwDemod]
% 0.86/1.00  --sup_immed_triv                        [TrivRules]
% 0.86/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.86/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_immed_bw_main                     []
% 0.86/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.86/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.86/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.86/1.00  
% 0.86/1.00  ------ Combination Options
% 0.86/1.00  
% 0.86/1.00  --comb_res_mult                         3
% 0.86/1.00  --comb_sup_mult                         2
% 0.86/1.00  --comb_inst_mult                        10
% 0.86/1.00  
% 0.86/1.00  ------ Debug Options
% 0.86/1.00  
% 0.86/1.00  --dbg_backtrace                         false
% 0.86/1.00  --dbg_dump_prop_clauses                 false
% 0.86/1.00  --dbg_dump_prop_clauses_file            -
% 0.86/1.00  --dbg_out_stat                          false
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  ------ Proving...
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  % SZS status Theorem for theBenchmark.p
% 0.86/1.00  
% 0.86/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.86/1.00  
% 0.86/1.00  fof(f2,axiom,(
% 0.86/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.00  
% 0.86/1.00  fof(f8,plain,(
% 0.86/1.00    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.86/1.00    inference(ennf_transformation,[],[f2])).
% 0.86/1.00  
% 0.86/1.00  fof(f9,plain,(
% 0.86/1.00    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.86/1.00    inference(flattening,[],[f8])).
% 0.86/1.00  
% 0.86/1.00  fof(f18,plain,(
% 0.86/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.86/1.00    inference(cnf_transformation,[],[f9])).
% 0.86/1.00  
% 0.86/1.00  fof(f4,conjecture,(
% 0.86/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.00  
% 0.86/1.00  fof(f5,negated_conjecture,(
% 0.86/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.86/1.00    inference(negated_conjecture,[],[f4])).
% 0.86/1.00  
% 0.86/1.00  fof(f12,plain,(
% 0.86/1.00    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.86/1.00    inference(ennf_transformation,[],[f5])).
% 0.86/1.00  
% 0.86/1.00  fof(f13,plain,(
% 0.86/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.86/1.00    inference(flattening,[],[f12])).
% 0.86/1.00  
% 0.86/1.00  fof(f15,plain,(
% 0.86/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK3,X0,X1) & v1_funct_1(sK3))) )),
% 0.86/1.00    introduced(choice_axiom,[])).
% 0.86/1.00  
% 0.86/1.00  fof(f14,plain,(
% 0.86/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.86/1.00    introduced(choice_axiom,[])).
% 0.86/1.00  
% 0.86/1.00  fof(f16,plain,(
% 0.86/1.00    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.86/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f15,f14])).
% 0.86/1.00  
% 0.86/1.00  fof(f25,plain,(
% 0.86/1.00    v1_funct_2(sK3,sK0,sK1)),
% 0.86/1.00    inference(cnf_transformation,[],[f16])).
% 0.86/1.00  
% 0.86/1.00  fof(f24,plain,(
% 0.86/1.00    v1_funct_1(sK3)),
% 0.86/1.00    inference(cnf_transformation,[],[f16])).
% 0.86/1.00  
% 0.86/1.00  fof(f26,plain,(
% 0.86/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.86/1.00    inference(cnf_transformation,[],[f16])).
% 0.86/1.00  
% 0.86/1.00  fof(f23,plain,(
% 0.86/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.86/1.00    inference(cnf_transformation,[],[f16])).
% 0.86/1.00  
% 0.86/1.00  fof(f22,plain,(
% 0.86/1.00    v1_funct_2(sK2,sK0,sK1)),
% 0.86/1.00    inference(cnf_transformation,[],[f16])).
% 0.86/1.00  
% 0.86/1.00  fof(f21,plain,(
% 0.86/1.00    v1_funct_1(sK2)),
% 0.86/1.00    inference(cnf_transformation,[],[f16])).
% 0.86/1.00  
% 0.86/1.00  fof(f3,axiom,(
% 0.86/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.00  
% 0.86/1.00  fof(f10,plain,(
% 0.86/1.00    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.86/1.00    inference(ennf_transformation,[],[f3])).
% 0.86/1.00  
% 0.86/1.00  fof(f11,plain,(
% 0.86/1.00    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.86/1.00    inference(flattening,[],[f10])).
% 0.86/1.00  
% 0.86/1.00  fof(f20,plain,(
% 0.86/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.86/1.00    inference(cnf_transformation,[],[f11])).
% 0.86/1.00  
% 0.86/1.00  fof(f27,plain,(
% 0.86/1.00    r1_partfun1(sK2,sK3)),
% 0.86/1.00    inference(cnf_transformation,[],[f16])).
% 0.86/1.00  
% 0.86/1.00  fof(f1,axiom,(
% 0.86/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.86/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.86/1.00  
% 0.86/1.00  fof(f6,plain,(
% 0.86/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.86/1.00    inference(ennf_transformation,[],[f1])).
% 0.86/1.00  
% 0.86/1.00  fof(f7,plain,(
% 0.86/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.86/1.00    inference(flattening,[],[f6])).
% 0.86/1.00  
% 0.86/1.00  fof(f17,plain,(
% 0.86/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.86/1.00    inference(cnf_transformation,[],[f7])).
% 0.86/1.00  
% 0.86/1.00  fof(f29,plain,(
% 0.86/1.00    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.86/1.00    inference(cnf_transformation,[],[f16])).
% 0.86/1.00  
% 0.86/1.00  fof(f19,plain,(
% 0.86/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.86/1.00    inference(cnf_transformation,[],[f9])).
% 0.86/1.00  
% 0.86/1.00  fof(f30,plain,(
% 0.86/1.00    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.86/1.00    inference(equality_resolution,[],[f19])).
% 0.86/1.00  
% 0.86/1.00  fof(f28,plain,(
% 0.86/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.86/1.00    inference(cnf_transformation,[],[f16])).
% 0.86/1.00  
% 0.86/1.00  cnf(c_2,plain,
% 0.86/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 0.86/1.00      | v1_partfun1(X0,X1)
% 0.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.86/1.00      | ~ v1_funct_1(X0)
% 0.86/1.00      | k1_xboole_0 = X2 ),
% 0.86/1.00      inference(cnf_transformation,[],[f18]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_8,negated_conjecture,
% 0.86/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 0.86/1.00      inference(cnf_transformation,[],[f25]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_216,plain,
% 0.86/1.00      ( v1_partfun1(X0,X1)
% 0.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.86/1.00      | ~ v1_funct_1(X0)
% 0.86/1.00      | sK3 != X0
% 0.86/1.00      | sK1 != X2
% 0.86/1.00      | sK0 != X1
% 0.86/1.00      | k1_xboole_0 = X2 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_217,plain,
% 0.86/1.00      ( v1_partfun1(sK3,sK0)
% 0.86/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.86/1.00      | ~ v1_funct_1(sK3)
% 0.86/1.00      | k1_xboole_0 = sK1 ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_216]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_9,negated_conjecture,
% 0.86/1.00      ( v1_funct_1(sK3) ),
% 0.86/1.00      inference(cnf_transformation,[],[f24]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_7,negated_conjecture,
% 0.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.86/1.00      inference(cnf_transformation,[],[f26]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_219,plain,
% 0.86/1.00      ( v1_partfun1(sK3,sK0) | k1_xboole_0 = sK1 ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_217,c_9,c_7]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_317,plain,
% 0.86/1.00      ( v1_partfun1(sK3,sK0) | k1_xboole_0 = sK1 ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_219]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_488,plain,
% 0.86/1.00      ( k1_xboole_0 = sK1 | v1_partfun1(sK3,sK0) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_10,negated_conjecture,
% 0.86/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.86/1.00      inference(cnf_transformation,[],[f23]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_11,negated_conjecture,
% 0.86/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 0.86/1.00      inference(cnf_transformation,[],[f22]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_230,plain,
% 0.86/1.00      ( v1_partfun1(X0,X1)
% 0.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.86/1.00      | ~ v1_funct_1(X0)
% 0.86/1.00      | sK2 != X0
% 0.86/1.00      | sK1 != X2
% 0.86/1.00      | sK0 != X1
% 0.86/1.00      | k1_xboole_0 = X2 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_231,plain,
% 0.86/1.00      ( v1_partfun1(sK2,sK0)
% 0.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.86/1.00      | ~ v1_funct_1(sK2)
% 0.86/1.00      | k1_xboole_0 = sK1 ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_230]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_12,negated_conjecture,
% 0.86/1.00      ( v1_funct_1(sK2) ),
% 0.86/1.00      inference(cnf_transformation,[],[f21]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_233,plain,
% 0.86/1.00      ( v1_partfun1(sK2,sK0) | k1_xboole_0 = sK1 ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_231,c_12,c_10]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_316,plain,
% 0.86/1.00      ( v1_partfun1(sK2,sK0) | k1_xboole_0 = sK1 ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_233]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_323,negated_conjecture,
% 0.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_482,plain,
% 0.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_3,plain,
% 0.86/1.00      ( ~ r1_partfun1(X0,X1)
% 0.86/1.00      | ~ v1_partfun1(X1,X2)
% 0.86/1.00      | ~ v1_partfun1(X0,X2)
% 0.86/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 0.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 0.86/1.00      | ~ v1_funct_1(X0)
% 0.86/1.00      | ~ v1_funct_1(X1)
% 0.86/1.00      | X1 = X0 ),
% 0.86/1.00      inference(cnf_transformation,[],[f20]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_6,negated_conjecture,
% 0.86/1.00      ( r1_partfun1(sK2,sK3) ),
% 0.86/1.00      inference(cnf_transformation,[],[f27]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_149,plain,
% 0.86/1.00      ( ~ v1_partfun1(X0,X1)
% 0.86/1.00      | ~ v1_partfun1(X2,X1)
% 0.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 0.86/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 0.86/1.00      | ~ v1_funct_1(X2)
% 0.86/1.00      | ~ v1_funct_1(X0)
% 0.86/1.00      | X0 = X2
% 0.86/1.00      | sK3 != X0
% 0.86/1.00      | sK2 != X2 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_6]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_150,plain,
% 0.86/1.00      ( ~ v1_partfun1(sK3,X0)
% 0.86/1.00      | ~ v1_partfun1(sK2,X0)
% 0.86/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.86/1.00      | ~ v1_funct_1(sK3)
% 0.86/1.00      | ~ v1_funct_1(sK2)
% 0.86/1.00      | sK3 = sK2 ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_149]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_154,plain,
% 0.86/1.00      ( ~ v1_partfun1(sK3,X0)
% 0.86/1.00      | ~ v1_partfun1(sK2,X0)
% 0.86/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.86/1.00      | sK3 = sK2 ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_150,c_12,c_9]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_320,plain,
% 0.86/1.00      ( ~ v1_partfun1(sK3,X0_42)
% 0.86/1.00      | ~ v1_partfun1(sK2,X0_42)
% 0.86/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42)))
% 0.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42)))
% 0.86/1.00      | sK3 = sK2 ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_154]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_485,plain,
% 0.86/1.00      ( sK3 = sK2
% 0.86/1.00      | v1_partfun1(sK3,X0_42) != iProver_top
% 0.86/1.00      | v1_partfun1(sK2,X0_42) != iProver_top
% 0.86/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top
% 0.86/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_326,plain,( X0_41 = X0_41 ),theory(equality) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_341,plain,
% 0.86/1.00      ( sK2 = sK2 ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_326]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_0,plain,
% 0.86/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 0.86/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.86/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.86/1.00      inference(cnf_transformation,[],[f17]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_4,negated_conjecture,
% 0.86/1.00      ( ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
% 0.86/1.00      inference(cnf_transformation,[],[f29]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_128,plain,
% 0.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.86/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.86/1.00      | sK3 != X3
% 0.86/1.00      | sK2 != X3
% 0.86/1.00      | sK1 != X2
% 0.86/1.00      | sK0 != X1 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_129,plain,
% 0.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.86/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.86/1.00      | sK2 != sK3 ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_128]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_133,plain,
% 0.86/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.86/1.00      | sK2 != sK3 ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_129,c_7]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_321,plain,
% 0.86/1.00      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.86/1.00      | sK2 != sK3 ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_133]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_348,plain,
% 0.86/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.86/1.00      | sK2 != sK3 ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_321]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_350,plain,
% 0.86/1.00      ( sK3 = sK2
% 0.86/1.00      | v1_partfun1(sK3,X0_42) != iProver_top
% 0.86/1.00      | v1_partfun1(sK2,X0_42) != iProver_top
% 0.86/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top
% 0.86/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_330,plain,
% 0.86/1.00      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 0.86/1.00      theory(equality) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_558,plain,
% 0.86/1.00      ( sK3 != X0_41 | sK2 != X0_41 | sK2 = sK3 ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_330]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_559,plain,
% 0.86/1.00      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_558]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_672,plain,
% 0.86/1.00      ( v1_partfun1(sK3,X0_42) != iProver_top
% 0.86/1.00      | v1_partfun1(sK2,X0_42) != iProver_top
% 0.86/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top
% 0.86/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_42,X1_42))) != iProver_top ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_485,c_10,c_341,c_348,c_350,c_559]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_682,plain,
% 0.86/1.00      ( v1_partfun1(sK3,sK0) != iProver_top
% 0.86/1.00      | v1_partfun1(sK2,sK0) != iProver_top
% 0.86/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 0.86/1.00      inference(superposition,[status(thm)],[c_482,c_672]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_683,plain,
% 0.86/1.00      ( ~ v1_partfun1(sK3,sK0)
% 0.86/1.00      | ~ v1_partfun1(sK2,sK0)
% 0.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.86/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_682]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_710,plain,
% 0.86/1.00      ( k1_xboole_0 = sK1 ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_488,c_10,c_7,c_341,c_348,c_317,c_316,c_559,c_605]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_1,plain,
% 0.86/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 0.86/1.00      | v1_partfun1(X0,k1_xboole_0)
% 0.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.86/1.00      | ~ v1_funct_1(X0) ),
% 0.86/1.00      inference(cnf_transformation,[],[f30]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_199,plain,
% 0.86/1.00      ( v1_partfun1(X0,k1_xboole_0)
% 0.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.86/1.00      | ~ v1_funct_1(X0)
% 0.86/1.00      | sK2 != X0
% 0.86/1.00      | sK1 != X1
% 0.86/1.00      | sK0 != k1_xboole_0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_200,plain,
% 0.86/1.00      ( v1_partfun1(sK2,k1_xboole_0)
% 0.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 0.86/1.00      | ~ v1_funct_1(sK2)
% 0.86/1.00      | sK0 != k1_xboole_0 ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_199]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_202,plain,
% 0.86/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 0.86/1.00      | v1_partfun1(sK2,k1_xboole_0)
% 0.86/1.00      | sK0 != k1_xboole_0 ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_200,c_12]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_203,plain,
% 0.86/1.00      ( v1_partfun1(sK2,k1_xboole_0)
% 0.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 0.86/1.00      | sK0 != k1_xboole_0 ),
% 0.86/1.00      inference(renaming,[status(thm)],[c_202]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_318,plain,
% 0.86/1.00      ( v1_partfun1(sK2,k1_xboole_0)
% 0.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 0.86/1.00      | sK0 != k1_xboole_0 ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_203]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_487,plain,
% 0.86/1.00      ( sK0 != k1_xboole_0
% 0.86/1.00      | v1_partfun1(sK2,k1_xboole_0) = iProver_top
% 0.86/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_5,negated_conjecture,
% 0.86/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 0.86/1.00      inference(cnf_transformation,[],[f28]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_324,negated_conjecture,
% 0.86/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_354,plain,
% 0.86/1.00      ( sK0 != k1_xboole_0
% 0.86/1.00      | v1_partfun1(sK2,k1_xboole_0) = iProver_top
% 0.86/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_549,plain,
% 0.86/1.00      ( ~ v1_partfun1(sK3,sK0)
% 0.86/1.00      | ~ v1_partfun1(sK2,sK0)
% 0.86/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_42)))
% 0.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_42)))
% 0.86/1.00      | sK3 = sK2 ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_320]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_605,plain,
% 0.86/1.00      ( ~ v1_partfun1(sK3,sK0)
% 0.86/1.00      | ~ v1_partfun1(sK2,sK0)
% 0.86/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.86/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.86/1.00      | sK3 = sK2 ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_549]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_331,plain,
% 0.86/1.00      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 0.86/1.00      theory(equality) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_560,plain,
% 0.86/1.00      ( sK0 != X0_42 | sK0 = k1_xboole_0 | k1_xboole_0 != X0_42 ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_331]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_610,plain,
% 0.86/1.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_560]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_327,plain,( X0_42 = X0_42 ),theory(equality) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_611,plain,
% 0.86/1.00      ( sK0 = sK0 ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_327]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_628,plain,
% 0.86/1.00      ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
% 0.86/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_487,c_10,c_7,c_341,c_324,c_348,c_354,c_317,c_316,
% 0.86/1.00                 c_559,c_605,c_610,c_611]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_713,plain,
% 0.86/1.00      ( v1_partfun1(sK2,k1_xboole_0) = iProver_top
% 0.86/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 0.86/1.00      inference(demodulation,[status(thm)],[c_710,c_628]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_322,negated_conjecture,
% 0.86/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_483,plain,
% 0.86/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_715,plain,
% 0.86/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 0.86/1.00      inference(demodulation,[status(thm)],[c_710,c_483]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_717,plain,
% 0.86/1.00      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 0.86/1.00      inference(demodulation,[status(thm)],[c_710,c_324]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_718,plain,
% 0.86/1.00      ( sK0 = k1_xboole_0 ),
% 0.86/1.00      inference(equality_resolution_simp,[status(thm)],[c_717]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_724,plain,
% 0.86/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 0.86/1.00      inference(light_normalisation,[status(thm)],[c_715,c_718]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_733,plain,
% 0.86/1.00      ( v1_partfun1(sK2,k1_xboole_0) = iProver_top ),
% 0.86/1.00      inference(forward_subsumption_resolution,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_713,c_724]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_182,plain,
% 0.86/1.00      ( v1_partfun1(X0,k1_xboole_0)
% 0.86/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.86/1.00      | ~ v1_funct_1(X0)
% 0.86/1.00      | sK3 != X0
% 0.86/1.00      | sK1 != X1
% 0.86/1.00      | sK0 != k1_xboole_0 ),
% 0.86/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_183,plain,
% 0.86/1.00      ( v1_partfun1(sK3,k1_xboole_0)
% 0.86/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 0.86/1.00      | ~ v1_funct_1(sK3)
% 0.86/1.00      | sK0 != k1_xboole_0 ),
% 0.86/1.00      inference(unflattening,[status(thm)],[c_182]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_185,plain,
% 0.86/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 0.86/1.00      | v1_partfun1(sK3,k1_xboole_0)
% 0.86/1.00      | sK0 != k1_xboole_0 ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_183,c_9]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_186,plain,
% 0.86/1.00      ( v1_partfun1(sK3,k1_xboole_0)
% 0.86/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 0.86/1.00      | sK0 != k1_xboole_0 ),
% 0.86/1.00      inference(renaming,[status(thm)],[c_185]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_319,plain,
% 0.86/1.00      ( v1_partfun1(sK3,k1_xboole_0)
% 0.86/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 0.86/1.00      | sK0 != k1_xboole_0 ),
% 0.86/1.00      inference(subtyping,[status(esa)],[c_186]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_486,plain,
% 0.86/1.00      ( sK0 != k1_xboole_0
% 0.86/1.00      | v1_partfun1(sK3,k1_xboole_0) = iProver_top
% 0.86/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_353,plain,
% 0.86/1.00      ( sK0 != k1_xboole_0
% 0.86/1.00      | v1_partfun1(sK3,k1_xboole_0) = iProver_top
% 0.86/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 0.86/1.00      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_621,plain,
% 0.86/1.00      ( v1_partfun1(sK3,k1_xboole_0) = iProver_top
% 0.86/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 0.86/1.00      inference(global_propositional_subsumption,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_486,c_10,c_7,c_341,c_324,c_348,c_353,c_317,c_316,
% 0.86/1.00                 c_559,c_605,c_610,c_611]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_714,plain,
% 0.86/1.00      ( v1_partfun1(sK3,k1_xboole_0) = iProver_top
% 0.86/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 0.86/1.00      inference(demodulation,[status(thm)],[c_710,c_621]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_716,plain,
% 0.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 0.86/1.00      inference(demodulation,[status(thm)],[c_710,c_482]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_721,plain,
% 0.86/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 0.86/1.00      inference(light_normalisation,[status(thm)],[c_716,c_718]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_729,plain,
% 0.86/1.00      ( v1_partfun1(sK3,k1_xboole_0) = iProver_top ),
% 0.86/1.00      inference(forward_subsumption_resolution,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_714,c_721]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(c_352,plain,
% 0.86/1.00      ( sK3 = sK2
% 0.86/1.00      | v1_partfun1(sK3,k1_xboole_0) != iProver_top
% 0.86/1.00      | v1_partfun1(sK2,k1_xboole_0) != iProver_top
% 0.86/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 0.86/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 0.86/1.00      inference(instantiation,[status(thm)],[c_350]) ).
% 0.86/1.00  
% 0.86/1.00  cnf(contradiction,plain,
% 0.86/1.00      ( $false ),
% 0.86/1.00      inference(minisat,
% 0.86/1.00                [status(thm)],
% 0.86/1.00                [c_733,c_729,c_724,c_721,c_559,c_352,c_348,c_341,c_10]) ).
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.86/1.00  
% 0.86/1.00  ------                               Statistics
% 0.86/1.00  
% 0.86/1.00  ------ General
% 0.86/1.00  
% 0.86/1.00  abstr_ref_over_cycles:                  0
% 0.86/1.00  abstr_ref_under_cycles:                 0
% 0.86/1.00  gc_basic_clause_elim:                   0
% 0.86/1.00  forced_gc_time:                         0
% 0.86/1.00  parsing_time:                           0.008
% 0.86/1.00  unif_index_cands_time:                  0.
% 0.86/1.00  unif_index_add_time:                    0.
% 0.86/1.00  orderings_time:                         0.
% 0.86/1.00  out_proof_time:                         0.009
% 0.86/1.00  total_time:                             0.055
% 0.86/1.00  num_of_symbols:                         45
% 0.86/1.00  num_of_terms:                           688
% 0.86/1.00  
% 0.86/1.00  ------ Preprocessing
% 0.86/1.00  
% 0.86/1.00  num_of_splits:                          0
% 0.86/1.00  num_of_split_atoms:                     0
% 0.86/1.00  num_of_reused_defs:                     0
% 0.86/1.00  num_eq_ax_congr_red:                    1
% 0.86/1.00  num_of_sem_filtered_clauses:            1
% 0.86/1.00  num_of_subtypes:                        4
% 0.86/1.00  monotx_restored_types:                  0
% 0.86/1.00  sat_num_of_epr_types:                   0
% 0.86/1.00  sat_num_of_non_cyclic_types:            0
% 0.86/1.00  sat_guarded_non_collapsed_types:        0
% 0.86/1.00  num_pure_diseq_elim:                    0
% 0.86/1.00  simp_replaced_by:                       0
% 0.86/1.00  res_preprocessed:                       61
% 0.86/1.00  prep_upred:                             0
% 0.86/1.00  prep_unflattend:                        15
% 0.86/1.00  smt_new_axioms:                         0
% 0.86/1.00  pred_elim_cands:                        2
% 0.86/1.00  pred_elim:                              4
% 0.86/1.00  pred_elim_cl:                           4
% 0.86/1.00  pred_elim_cycles:                       6
% 0.86/1.00  merged_defs:                            0
% 0.86/1.00  merged_defs_ncl:                        0
% 0.86/1.00  bin_hyper_res:                          0
% 0.86/1.00  prep_cycles:                            4
% 0.86/1.00  pred_elim_time:                         0.003
% 0.86/1.00  splitting_time:                         0.
% 0.86/1.00  sem_filter_time:                        0.
% 0.86/1.00  monotx_time:                            0.
% 0.86/1.00  subtype_inf_time:                       0.
% 0.86/1.00  
% 0.86/1.00  ------ Problem properties
% 0.86/1.00  
% 0.86/1.00  clauses:                                9
% 0.86/1.00  conjectures:                            3
% 0.86/1.00  epr:                                    3
% 0.86/1.00  horn:                                   7
% 0.86/1.00  ground:                                 7
% 0.86/1.00  unary:                                  2
% 0.86/1.00  binary:                                 4
% 0.86/1.00  lits:                                   21
% 0.86/1.00  lits_eq:                                8
% 0.86/1.00  fd_pure:                                0
% 0.86/1.00  fd_pseudo:                              0
% 0.86/1.00  fd_cond:                                0
% 0.86/1.00  fd_pseudo_cond:                         0
% 0.86/1.00  ac_symbols:                             0
% 0.86/1.00  
% 0.86/1.00  ------ Propositional Solver
% 0.86/1.00  
% 0.86/1.00  prop_solver_calls:                      24
% 0.86/1.00  prop_fast_solver_calls:                 355
% 0.86/1.00  smt_solver_calls:                       0
% 0.86/1.00  smt_fast_solver_calls:                  0
% 0.86/1.00  prop_num_of_clauses:                    194
% 0.86/1.00  prop_preprocess_simplified:             1226
% 0.86/1.00  prop_fo_subsumed:                       16
% 0.86/1.00  prop_solver_time:                       0.
% 0.86/1.00  smt_solver_time:                        0.
% 0.86/1.00  smt_fast_solver_time:                   0.
% 0.86/1.00  prop_fast_solver_time:                  0.
% 0.86/1.00  prop_unsat_core_time:                   0.
% 0.86/1.00  
% 0.86/1.00  ------ QBF
% 0.86/1.00  
% 0.86/1.00  qbf_q_res:                              0
% 0.86/1.00  qbf_num_tautologies:                    0
% 0.86/1.00  qbf_prep_cycles:                        0
% 0.86/1.00  
% 0.86/1.00  ------ BMC1
% 0.86/1.00  
% 0.86/1.00  bmc1_current_bound:                     -1
% 0.86/1.00  bmc1_last_solved_bound:                 -1
% 0.86/1.00  bmc1_unsat_core_size:                   -1
% 0.86/1.00  bmc1_unsat_core_parents_size:           -1
% 0.86/1.00  bmc1_merge_next_fun:                    0
% 0.86/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.86/1.00  
% 0.86/1.00  ------ Instantiation
% 0.86/1.00  
% 0.86/1.00  inst_num_of_clauses:                    51
% 0.86/1.00  inst_num_in_passive:                    9
% 0.86/1.00  inst_num_in_active:                     42
% 0.86/1.00  inst_num_in_unprocessed:                0
% 0.86/1.00  inst_num_of_loops:                      50
% 0.86/1.00  inst_num_of_learning_restarts:          0
% 0.86/1.00  inst_num_moves_active_passive:          6
% 0.86/1.00  inst_lit_activity:                      0
% 0.86/1.00  inst_lit_activity_moves:                0
% 0.86/1.00  inst_num_tautologies:                   0
% 0.86/1.00  inst_num_prop_implied:                  0
% 0.86/1.00  inst_num_existing_simplified:           0
% 0.86/1.00  inst_num_eq_res_simplified:             0
% 0.86/1.00  inst_num_child_elim:                    0
% 0.86/1.00  inst_num_of_dismatching_blockings:      1
% 0.86/1.00  inst_num_of_non_proper_insts:           30
% 0.86/1.00  inst_num_of_duplicates:                 0
% 0.86/1.00  inst_inst_num_from_inst_to_res:         0
% 0.86/1.00  inst_dismatching_checking_time:         0.
% 0.86/1.00  
% 0.86/1.00  ------ Resolution
% 0.86/1.00  
% 0.86/1.00  res_num_of_clauses:                     0
% 0.86/1.00  res_num_in_passive:                     0
% 0.86/1.00  res_num_in_active:                      0
% 0.86/1.00  res_num_of_loops:                       65
% 0.86/1.00  res_forward_subset_subsumed:            6
% 0.86/1.00  res_backward_subset_subsumed:           0
% 0.86/1.00  res_forward_subsumed:                   0
% 0.86/1.00  res_backward_subsumed:                  0
% 0.86/1.00  res_forward_subsumption_resolution:     0
% 0.86/1.00  res_backward_subsumption_resolution:    0
% 0.86/1.00  res_clause_to_clause_subsumption:       16
% 0.86/1.00  res_orphan_elimination:                 0
% 0.86/1.00  res_tautology_del:                      5
% 0.86/1.00  res_num_eq_res_simplified:              0
% 0.86/1.00  res_num_sel_changes:                    0
% 0.86/1.00  res_moves_from_active_to_pass:          0
% 0.86/1.00  
% 0.86/1.00  ------ Superposition
% 0.86/1.00  
% 0.86/1.00  sup_time_total:                         0.
% 0.86/1.00  sup_time_generating:                    0.
% 0.86/1.00  sup_time_sim_full:                      0.
% 0.86/1.00  sup_time_sim_immed:                     0.
% 0.86/1.00  
% 0.86/1.00  sup_num_of_clauses:                     9
% 0.86/1.00  sup_num_in_active:                      3
% 0.86/1.00  sup_num_in_passive:                     6
% 0.86/1.00  sup_num_of_loops:                       8
% 0.86/1.00  sup_fw_superposition:                   1
% 0.86/1.00  sup_bw_superposition:                   0
% 0.86/1.00  sup_immediate_simplified:               4
% 0.86/1.00  sup_given_eliminated:                   0
% 0.86/1.00  comparisons_done:                       0
% 0.86/1.00  comparisons_avoided:                    0
% 0.86/1.00  
% 0.86/1.00  ------ Simplifications
% 0.86/1.00  
% 0.86/1.00  
% 0.86/1.00  sim_fw_subset_subsumed:                 0
% 0.86/1.00  sim_bw_subset_subsumed:                 1
% 0.86/1.00  sim_fw_subsumed:                        0
% 0.86/1.00  sim_bw_subsumed:                        0
% 0.86/1.00  sim_fw_subsumption_res:                 2
% 0.86/1.00  sim_bw_subsumption_res:                 0
% 0.86/1.00  sim_tautology_del:                      0
% 0.86/1.00  sim_eq_tautology_del:                   0
% 0.86/1.00  sim_eq_res_simp:                        1
% 0.86/1.00  sim_fw_demodulated:                     0
% 0.86/1.00  sim_bw_demodulated:                     5
% 0.86/1.00  sim_light_normalised:                   2
% 0.86/1.00  sim_joinable_taut:                      0
% 0.86/1.00  sim_joinable_simp:                      0
% 0.86/1.00  sim_ac_normalised:                      0
% 0.86/1.00  sim_smt_subsumption:                    0
% 0.86/1.00  
%------------------------------------------------------------------------------
