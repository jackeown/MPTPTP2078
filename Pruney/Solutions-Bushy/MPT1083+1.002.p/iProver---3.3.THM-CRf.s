%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1083+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:51 EST 2020

% Result     : Theorem 1.40s
% Output     : CNFRefutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 182 expanded)
%              Number of clauses        :   60 (  66 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   20
%              Number of atoms          :  294 ( 851 expanded)
%              Number of equality atoms :  143 ( 243 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
             => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0) )
           => ! [X2] :
                ( ( v5_relat_1(X2,X0)
                  & v1_relat_1(X2) )
               => k1_relat_1(X2) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
     => ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X1))
        & v5_relat_1(sK2,X0)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0) )
     => ( ? [X2] :
            ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,sK1))
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK1,X0,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
                & v5_relat_1(X2,X0)
                & v1_relat_1(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_relat_1(X2) != k1_relat_1(k5_relat_1(X2,X1))
              & v5_relat_1(X2,sK0)
              & v1_relat_1(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X1,sK0,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1))
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f25,f24,f23])).

fof(f44,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f40,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_14,negated_conjecture,
    ( v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_216,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_14])).

cnf(c_217,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_219,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_217,c_15])).

cnf(c_536,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(subtyping,[status(esa)],[c_219])).

cnf(c_661,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_263,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK1 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_264,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | k1_relset_1(X0,X1,sK1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_417,plain,
    ( k1_relset_1(X0,X1,sK1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK0 != X1
    | sK0 != X0
    | sK1 != sK1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_264])).

cnf(c_418,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_475,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_418])).

cnf(c_531,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | k1_xboole_0 = sK0 ),
    inference(subtyping,[status(esa)],[c_475])).

cnf(c_9,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_18,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_209,plain,
    ( sK0 != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_537,plain,
    ( sK0 != o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_209])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_204,plain,
    ( o_0_0_xboole_0 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_205,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_538,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_205])).

cnf(c_667,plain,
    ( sK0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_537,c_538])).

cnf(c_547,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_720,plain,
    ( sK0 != X0_45
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0_45 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_773,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_543,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_774,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_796,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_667,c_773,c_774])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_254,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_255,plain,
    ( k1_relset_1(X0,X1,sK1) = k1_relat_1(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_535,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | k1_relset_1(X0_45,X1_45,sK1) = k1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_255])).

cnf(c_728,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(equality_resolution,[status(thm)],[c_535])).

cnf(c_799,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_796,c_728])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_541,plain,
    ( ~ r1_tarski(k2_relat_1(X0_45),k1_relat_1(X1_45))
    | ~ v1_relat_1(X1_45)
    | ~ v1_relat_1(X0_45)
    | k1_relat_1(k5_relat_1(X0_45,X1_45)) = k1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_659,plain,
    ( k1_relat_1(k5_relat_1(X0_45,X1_45)) = k1_relat_1(X0_45)
    | r1_tarski(k2_relat_1(X0_45),k1_relat_1(X1_45)) != iProver_top
    | v1_relat_1(X1_45) != iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_877,plain,
    ( k1_relat_1(k5_relat_1(X0_45,sK1)) = k1_relat_1(X0_45)
    | r1_tarski(k2_relat_1(X0_45),sK0) != iProver_top
    | v1_relat_1(X0_45) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_799,c_659])).

cnf(c_544,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_707,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_299,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_300,plain,
    ( v1_relat_1(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_534,plain,
    ( v1_relat_1(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(subtyping,[status(esa)],[c_300])).

cnf(c_709,plain,
    ( v1_relat_1(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_710,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_882,plain,
    ( v1_relat_1(X0_45) != iProver_top
    | r1_tarski(k2_relat_1(X0_45),sK0) != iProver_top
    | k1_relat_1(k5_relat_1(X0_45,sK1)) = k1_relat_1(X0_45) ),
    inference(global_propositional_subsumption,[status(thm)],[c_877,c_707,c_710])).

cnf(c_883,plain,
    ( k1_relat_1(k5_relat_1(X0_45,sK1)) = k1_relat_1(X0_45)
    | r1_tarski(k2_relat_1(X0_45),sK0) != iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(renaming,[status(thm)],[c_882])).

cnf(c_891,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_661,c_883])).

cnf(c_746,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_722,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) != X0_45
    | k1_relat_1(sK2) != X0_45
    | k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_745,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK1)) != k1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,sK1))
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_13,negated_conjecture,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_540,negated_conjecture,
    ( k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_22,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_891,c_746,c_745,c_540,c_22])).


%------------------------------------------------------------------------------
